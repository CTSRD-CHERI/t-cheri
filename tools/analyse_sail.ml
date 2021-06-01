open Ast
open Ast_defs
open Ast_util
open Rewriter

let opt_splice = ref ([]:string list)

type fun_info =
  { typquant : typquant;
    args : (id * typ) list;
    ret_typ : typ;
    effect : effect;
    calls : IdSet.t;
    regs_read : IdSet.t;
    regs_read_no_exc : IdSet.t;
    regs_written : IdSet.t;
    regs_written_no_exc : IdSet.t;
    trans_calls : IdSet.t;
    trans_regs_read : IdSet.t;
    trans_regs_read_no_exc : IdSet.t;
    trans_regs_written : IdSet.t;
    trans_regs_written_no_exc : IdSet.t }

let called_funs_in_exp exp =
  (fold_exp
     { (pure_exp_alg IdSet.empty IdSet.union) with
       e_app = (fun (id, ids) -> List.fold_left IdSet.union (IdSet.singleton id) ids);
       e_app_infix = (fun (ids1, id, ids2) -> IdSet.union (IdSet.singleton id) (IdSet.union ids1 ids2));
       lEXP_memory = (fun (id, ids) -> List.fold_left IdSet.union (IdSet.singleton id) ids) }
     exp)

let regs_read_in_exp exp =
  let e_id id = match Type_check.Env.lookup_id id (Type_check.env_of exp) with
    | Register _ -> IdSet.singleton id
    | _ ->
       (* TODO Handle register references *)
       IdSet.empty
  in
  fold_exp
    { (pure_exp_alg IdSet.empty IdSet.union) with e_id = e_id; e_ref = e_id }
    exp

let regs_written_in_exp exp =
  let open Type_check in
  let reg_idset id =
    if Env.is_register id (env_of exp)
    then IdSet.singleton id
    else IdSet.empty
  in
  fold_exp
    { (pure_exp_alg IdSet.empty IdSet.union) with
      e_ref = reg_idset;
      lEXP_id = reg_idset;
      lEXP_cast = (fun (_, id) -> reg_idset id);
      lEXP_field = (fun (ids, id) -> IdSet.union ids (reg_idset id)) }
    exp

let exp_fails exception_funs exp =
  (* First replace assert(false) with a more obviously failing expression
     so that we can then use pure_exp_alg below *)
  let is_false_exp = function
    | E_aux (E_lit (L_aux (L_false, _)), _) -> true
    | _ -> false
  in
  let exp =
    fold_exp
      { id_exp_alg with
        e_assert = (fun (e, msg) -> if is_false_exp e then E_throw e else E_assert (e, msg)) }
      exp
  in
  fold_exp
    { (pure_exp_alg false (||)) with
      e_throw = (fun _ -> true);
      e_exit = (fun _ -> true);
      e_app = (fun (id, es) -> List.fold_left (||) (IdSet.mem id exception_funs) es);
      e_app_infix = (fun (e1, id, e2) -> e1 || IdSet.mem id exception_funs || e2);
      e_if = (fun (c, e1, e2) -> c || (e1 && e2));
      e_case = (fun (e, cases) -> e || (cases <> [] && List.fold_left (&&) true cases));
      (* try-catch might or might not fail, but for our analysis non-failure is the conservative answer *)
      e_try = (fun _ -> false) }
    exp

let add_exception_fun exception_funs = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _) as fd) ->
     let id = id_of_fundef fd in
     let pexp_fails pexp =
       let (_, guard, exp, _) = destruct_pexp pexp in
       exp_fails exception_funs exp || (match guard with Some exp -> exp_fails exception_funs exp | _ -> false)
     in
     let funcl_fails (FCL_aux (FCL_Funcl (_, p), _)) = pexp_fails p in
     if List.for_all funcl_fails funcls then IdSet.add id exception_funs else exception_funs
  | _ -> exception_funs

let exception_funs ast = List.fold_left add_exception_fun IdSet.empty ast.defs

let false_exp = mk_exp (E_lit (L_aux (L_false, Parse_ast.Unknown)))
let true_exp = mk_exp (E_lit (L_aux (L_true, Parse_ast.Unknown)))
let mk_conj a b = mk_exp (E_app (mk_id "and_bool_no_flow", [a; b]))
let mk_disj a b = mk_exp (E_app (mk_id "or_bool_no_flow", [a; b]))

let rec mk_conjs = function
  | [] -> true_exp
  | [x] -> x
  | (x :: xs) -> mk_conj x (mk_conjs xs)

let throw_is_failure = function
  | E_aux (E_app (id, _), _) -> string_of_id id = "Error_Undefined"
  | _ -> false

let ids_present ids =
  fold_exp { (pure_exp_alg false (||)) with
    e_id = fun id -> IdSet.mem id ids
  }

let ids_not_present ids exp = not (ids_present ids exp)

let mk_t_e x = E_aux (x, (Parse_ast.Unknown, Type_check.empty_tannot))
let mk_t_eq x y = mk_t_e (E_app (mk_id "eq", [x; y]))
let mk_t_not a = mk_t_e (E_app (mk_id "not_bool", [a]))

let case_pat_exp_to_cond x = function
  | Pat_exp (P_aux (P_lit l, _), rhs) -> Some (mk_t_eq x (mk_t_e (E_lit l)), rhs)
  | Pat_when (P_aux (P_wild, _), c, rhs) -> Some (c, rhs)
  | Pat_when (P_aux (P_id id, _), c, rhs) -> Some (subst id x c, subst id x rhs)
  | _ -> None

let rec case_to_if_worker (x, ps) = match ps with
  | Pat_aux (Pat_exp (P_aux (P_wild, _), E_aux (rhs, _)), _) :: _ -> rhs
  | Pat_aux (Pat_exp (P_aux (P_id id, _), rhs), _) :: _ -> unaux_exp (subst id x rhs)
  | Pat_aux (p_exp, _) :: ps_tail -> begin match case_pat_exp_to_cond x p_exp with
    | None -> E_case (x, ps)
    | Some (c, rhs) -> E_if (c, rhs, mk_t_e (case_to_if_worker (x, ps_tail)))
  end
  | _ -> E_case (x, ps)

let rec lit_bits = function
  | (E_aux (E_lit l, _)) -> vector_string_to_bit_list l
  | (E_aux (E_cast (_, x), _)) -> lit_bits x
  | _ -> []

let vector_eq_lit_worker id args default =
  try
  let s_flip = if String.equal (string_of_id id) "eq_bits"
    then false
    else if String.equal (string_of_id id) "neq_bits"
    then true
    else invalid_arg "not eq_bits"
  in
  let v = function
    | (E_aux (E_vector [x], _)) -> Some x
    | _ -> None
  in
  let (x, y) = match List.map v args with
    | [Some x; None] -> (x, List.hd (List.rev args))
    | [None; Some x] -> (x, List.hd args)
    | _ -> invalid_arg "not vec"
  in
  let rec b = function
    | (E_aux (E_lit l, _)) -> begin match vector_string_to_bit_list l with
      | [L_aux (L_zero, _)] -> Some true
      | [L_aux (L_one, _)] -> Some false
      | _ -> None
    end
    | (E_aux (E_cast (_, x), _)) -> b x
    | _ -> None
  in
  let b_flip = Option.get (b y : bool option) in
  if Bool.equal s_flip b_flip
    then unaux_exp x
    else E_app (mk_id "not_bool", [x])
  with Invalid_argument _ -> default

let plet_id_worker = function
  | (P_aux (P_id id, _), (E_aux (E_id id2, _) as v), body) ->
    unaux_exp (subst id v body)
  | (p, exp, body) -> E_internal_plet (p, exp, body)

let let_id_worker = function
  | (LB_aux (LB_val (P_aux (P_id id, _), (E_aux (E_id id2, _) as v)), _), body) ->
    unaux_exp (subst id v body)
  | (lb, body) -> E_let (lb, body)

let case_if_simp = fold_exp { id_exp_alg with
    e_case = case_to_if_worker;
    e_app = (fun (id, args) -> vector_eq_lit_worker id args (E_app (id, args)));
    e_app_infix = (fun (lhs, id, rhs) -> vector_eq_lit_worker id
        [lhs; rhs] (E_app_infix (lhs, id, rhs)));
    e_let = let_id_worker;
    e_internal_plet = plet_id_worker }

let let_rhs_triv exp =
  fold_exp { (pure_exp_alg false (&&)) with
    e_id = (fun _ -> true);
    e_lit = (fun _ -> true)
  } exp

let drop_tannot exp = map_exp_annot (fun (l, _) -> (l, ())) exp

let filter_for_let fun_id ids assertions =
  let xs = List.filter (ids_not_present ids) assertions in
  let n = List.length assertions - List.length xs in
  if n > 0
  then prerr_endline ("dropped " ^ string_of_int n ^
    " assertions (" ^
    Util.string_of_list ", " string_of_id (IdSet.elements ids) ^ ") in " ^
    string_of_id fun_id)
  else ();
  xs

let apply_let_bind fun_id p body assertions = match p with
  | P_aux (P_id id, _) -> if let_rhs_triv body
    then List.map (subst id (drop_tannot body)) assertions
    else filter_for_let fun_id (pat_ids p) assertions
  | _ -> filter_for_let fun_id (pat_ids p) assertions

let preconds_verbose = true

let log_msg s = if preconds_verbose
  then prerr_endline s else ()

let precond_suffix = "_precondition"
let precond_name id = append_id id precond_suffix

let get_precond_args precond_funs id args = match Bindings.find_opt id precond_funs with
  | None -> None
  | Some None -> Some (precond_name id, args)
  | Some (Some []) -> Some (precond_name id, [])
  | Some (Some present) -> Some (precond_name id, List.map fst (List.filter snd
    (List.map2 (fun a b -> (a, b)) args present)))

let get_precond_app precond_funs id args =
  match get_precond_args precond_funs id args with
  | Some (id2, []) -> (log_msg ("including precond from " ^ string_of_id id2);
        [mk_exp (E_app (id2, [mk_lit_exp L_unit]))])
  | Some (id2, args2) -> (log_msg ("including precond from " ^ string_of_id id2);
        [mk_exp (E_app (id2, List.map drop_tannot args2))])
  | None -> []

let rec scan_assertions_aux nm precond_funs x =
  let scan = scan_assertions nm precond_funs in
  match x with
  | E_block es -> List.concat (List.map scan es)
  | E_assert (e, msg) -> [drop_tannot e]
  | E_if (c, x, y) -> begin match scan y with
    | [] -> []
    | xs -> [mk_disj (drop_tannot c) (mk_conjs xs)]
    end
  | E_cast (_, e) -> scan e
  | E_throw e -> if throw_is_failure e then [false_exp] else []
  | E_let (LB_aux (LB_val (p, e1), _), e2) ->
        scan e1 @ apply_let_bind nm p e1 (scan e2)
  | E_internal_plet (p, e1, e2) ->
        scan e1 @ apply_let_bind nm p e1 (scan e2)
  | E_app (id, args) -> get_precond_app precond_funs id args
  | E_app_infix (lhs, id, rhs) -> get_precond_app precond_funs id [lhs; rhs]
  | e -> []
  and scan_assertions nm fun_assertions (E_aux (exp, _)) =
    scan_assertions_aux nm fun_assertions exp

let def_note = function
  | DEF_fundef fd -> "fundef_of " ^ string_of_id (id_of_fundef fd)
  | DEF_spec spec -> "val spec of " ^ string_of_id (id_of_val_spec spec)
  | _ -> "other def"

(* sending preconds as smt queries *)
let rec smt_result chan = try
  let line = String.trim (input_line chan) in
  begin
  if String.equal line "unsat"
  then true
  else if String.equal line "sat"
  then false
  else if String.equal line "unsupported"
  then smt_result chan
  else (prerr_endline ("smt_result: unexpected: " ^ line); false)
  end
  with End_of_file ->
  (prerr_endline "smt_result: unexpected end of file"; false)

let precond_smt_check env ast fn_name ty_args =
  let pname = precond_name fn_name in
  let ast = Slice.filter_ast_ids (IdSet.singleton pname) IdSet.empty ast in
  let (ast, env) = Process_file.rewrite_ast_target "c" env ast in
  let (jdefs, jctxt, smt_ctxt) = Jib_smt.compile env ast in
  let file_name = "test_" ^ string_of_id pname ^ ".smt2" in
  Jib_smt.smt_query_to_file file_name jctxt smt_ctxt pname (ty_args, mk_id_typ (mk_id "bool"))
    "property" (Property.Q_all Property.Return) jdefs;
  let smt_in = Unix.open_process_in ("z3 -smt2 -T:2 " ^ file_name) in
  let res = smt_result smt_in in
  let _ = Unix.close_process_in smt_in in
  res

let rec pat_id_list = function
  | P_aux (P_id id, _) :: ps -> begin match pat_id_list ps with
    | None -> None
    | Some ids -> Some (id :: ids)
  end
  | [] -> Some []
  | _ -> None

let simplify_binding (p, body) = match p with
  | P_aux (P_tup xs, _) -> begin match pat_id_list xs with
    | None -> (p, None)
    | Some ys ->
      let ys_present = List.map (fun id -> (id,
            ids_present (IdSet.singleton id) body)) ys in
      let zs = List.map (fun (id, _) -> mk_pat (P_id id)) (List.filter snd ys_present) in
      let p2 = match zs with
        | [] -> mk_pat P_wild
        | [p] -> p
        | ps -> mk_pat (P_tup ps)
      in
      (p2, Some (List.map snd ys_present))
  end
  | P_aux (P_id id, _) -> if ids_present (IdSet.singleton id) body
    then (p, None)
    else (mk_pat P_wild, Some [])
  | P_aux (P_lit (L_aux (L_unit, _)), _) -> (p, None)
  | P_aux (_, (l, _)) ->
  raise (Reporting.err_general l ("fundef pattern not tup or id " ^ string_of_pat p))

let add_funcl_assertions ast data = function
  | FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (p, body), _)), (l, _)) ->
    log_msg ("scanning " ^ string_of_id id ^ " for preconditions");
    let (env, precond_defs, precond_funs) = data in
    let body2 = case_if_simp body in
    log_msg ("converted body");
    begin match scan_assertions id precond_funs body2 with
    | [] -> data
    | assns ->
      prerr_endline ("got a precondition for " ^ (string_of_id id));
      let assn = mk_conjs assns in
      let p2 = map_pat_annot (fun _ -> no_annot) p in
      let (q, typ) = Type_check.Env.get_val_spec_orig id env in
      let q_params = quant_items q in
      if List.length q_params > 0
      then
        (prerr_endline ("dropping precondition for " ^ string_of_id id ^
            ": type quantifiers: " ^
            Util.string_of_list ", " string_of_quant_item q_params);
            data)
      else
      let (p3, adj_args) = simplify_binding (p2, assn) in
      let pid = precond_name id in
      let fund = mk_fundef [mk_funcl pid p3 assn] in
      let ty_args = match unaux_typ typ with
        | Typ_fn (ty_args, _, _) -> ty_args
        | _ -> raise (Reporting.err_general Parse_ast.Unknown
                ("unexpected non-function type of " ^ string_of_id id))
      in
      let precond_funs2 = Bindings.add id adj_args precond_funs in
      let (_, ty_args2) = Option.get (get_precond_args precond_funs2 id ty_args) in
      let ty_args3 = match ty_args2 with
        | [] -> [unit_typ]
        | _ -> ty_args2
      in
      let typ2 = mk_typ (Typ_fn (ty_args3, bool_typ, no_effect)) in
      let spec = mk_val_spec (VS_val_spec (mk_typschm q typ2, pid, [], false)) in
      let (defs, env2) = try Type_check.check_defs env [spec; fund]
        with Type_check.Type_error (_, l, err) ->
         raise (Reporting.err_typ l (Type_error.string_of_type_error err))
      in
      let precond_defs2 = precond_defs @ defs in
      let _ = precond_smt_check env2 (append_ast_defs ast precond_defs2) id ty_args3 in
      (env2, precond_defs2, precond_funs2)
    end
  | FCL_aux (FCL_Funcl (id, pp), (l, _)) ->
    raise (Reporting.err_general l ("unexpected pat_exp shape of " ^ string_of_id id))

let add_fun_assertions ast data = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _)) ->
     List.fold_left (add_funcl_assertions ast) data funcls
 | _ -> data

let quote_funcl_def = function
  | FCL_aux (FCL_Funcl (id, pexp), (l, _)) ->
    prerr_endline ("def of " ^ string_of_id id ^ ": " ^ string_of_pexp pexp)

let quote_fundef_defs = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _)) ->
     List.iter quote_funcl_def funcls
  | _ -> ()

let rec tcheck env cdefs = function
  | [] -> (List.concat (List.concat (List.rev cdefs)), env)
  | (def :: defs) ->
  begin match def with
    | DEF_fundef fundef ->
        prerr_endline ("type checking fundef of " ^ string_of_id (id_of_fundef fundef))
    | _ -> ()
  end;
  quote_fundef_defs def;
  let env_defs = try Type_check.check_with_envs env [def]
    with Type_check.Type_error (_, l, err) ->
     raise (Reporting.err_typ l (Type_error.string_of_type_error err))
  in
  let def_cdefs = List.map fst env_defs in
  let env2 = snd (List.hd (List.rev env_defs)) in
  tcheck env2 (def_cdefs :: cdefs) defs

let get_preconds env ast =
  Reporting.opt_warnings := true;
  prerr_endline ("getting preconds for " ^ (string_of_int (List.length ast.defs)) ^ " ast elems");
  let (env2, precond_defs1, precond_funs) = List.fold_left (add_fun_assertions ast)
        (env, [], Bindings.empty) ast.defs in
  prerr_endline ("got " ^ string_of_int (List.length precond_defs1) ^ " precond ast elems");
  prerr_endline ("type checking ..");
  prerr_endline ("done with preconds.");
  (env2, List.rev precond_defs1, precond_funs)

let add_fun_infos_of_def env exception_funs fun_infos = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _) as fd) ->
     let id = id_of_fundef fd in
     let exp_of_pexp pexp =
       let (_, _, exp, _) = destruct_pexp pexp in
       exp
     in
     let arg_ids = match funcls with
       | [FCL_aux (FCL_Funcl (_, pexp), _)] ->
          let (pat, _, _, _) = destruct_pexp pexp in
          begin match unaux_pat pat with
            | P_id id -> Some [id]
            | P_tup pats ->
               let get_id = function P_id id -> Some id | _ -> None in
               List.map unaux_pat pats |> List.map get_id |> Util.option_all
            | _ -> None
          end
       | _ -> None
     in
     let exp_of_funcl (FCL_aux (FCL_Funcl (_, p), _)) = exp_of_pexp p in
     let exps = List.map exp_of_funcl funcls in
     let merge = List.fold_left IdSet.union IdSet.empty in
     let calls = merge (List.map called_funs_in_exp exps) in
     let calls_infos = Bindings.filter (fun id  _ -> IdSet.mem id calls) fun_infos in
     let regs_read = merge (List.map regs_read_in_exp exps) in
     let regs_read_no_exc = if IdSet.mem id exception_funs then IdSet.empty else regs_read in
     let regs_written = merge (List.map regs_written_in_exp exps) in
     let regs_written_no_exc = if IdSet.mem id exception_funs then IdSet.empty else regs_written in
     let trans_calls =
       List.map (fun (_, info) -> info.trans_calls) (Bindings.bindings calls_infos)
       |> List.fold_left IdSet.union calls
     in
     let trans_regs_read =
       List.map (fun (_, info) -> info.trans_regs_read) (Bindings.bindings calls_infos)
       |> List.fold_left IdSet.union regs_read
     in
     let trans_regs_read_no_exc =
       if IdSet.mem id exception_funs then
         IdSet.empty
       else
         List.map (fun (_, info) -> info.trans_regs_read_no_exc) (Bindings.bindings calls_infos)
         |> List.fold_left IdSet.union regs_read
     in
     let trans_regs_written =
       List.map (fun (_, info) -> info.trans_regs_written) (Bindings.bindings calls_infos)
       |> List.fold_left IdSet.union regs_written
     in
     let trans_regs_written_no_exc =
       if IdSet.mem id exception_funs then
         IdSet.empty
       else
         List.map (fun (_, info) -> info.trans_regs_written_no_exc) (Bindings.bindings calls_infos)
         |> List.fold_left IdSet.union regs_written
     in
     let typquant, arg_typs, ret_typ, effect = match Type_check.Env.get_val_spec_orig id env with
       | typquant, Typ_aux (Typ_fn (arg_typs, ret_typ, effect), _) -> typquant, arg_typs, ret_typ, effect
       | _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ ("Function " ^ string_of_id id ^ " does not have function type"))
     in
     let args = match arg_ids with
       | Some ids when List.length ids = List.length arg_typs -> List.combine ids arg_typs
       | _ ->
          List.mapi (fun i typ -> (mk_id ("arg" ^ string_of_int i), typ)) arg_typs
     in
     Bindings.add id
       {
         typquant; args; ret_typ; effect; calls; regs_read; regs_read_no_exc; regs_written; regs_written_no_exc;
         trans_calls; trans_regs_read; trans_regs_read_no_exc; trans_regs_written; trans_regs_written_no_exc
       }
       fun_infos
  | DEF_internal_mutrec _ ->
     raise (Reporting.err_todo Parse_ast.Unknown "Analysis of mutually recursive functions not implemented")
  | _ -> fun_infos

let fun_ids ast = List.concat (List.map (function DEF_fundef fd -> [id_of_fundef fd] | _ -> []) ast.defs)

let fun_infos_of_ast env ast =
  let exc_funs = exception_funs ast in
  List.fold_left (add_fun_infos_of_def env exc_funs) Bindings.empty ast.defs

let load_files ?mutrecs:(mutrecs=IdSet.empty) files =
  let open Process_file in
  Nl_flow.opt_nl_flow := true;
  Process_file.opt_memo_z3 := true;
  Reporting.opt_warnings := false;
  Initial_check.opt_undefined_gen := true;
  Type_check.opt_no_effects := true;
  Rewrites.opt_mono_rewrites := true;
  Rewrites.opt_auto_mono := true;
  Pretty_print_lem.opt_mwords := true;
  Constant_propagation_mutrec.targets := IdSet.elements mutrecs;
  Util.opt_verbosity := 1;

  let (_, ast, env) = load_files [] Type_check.initial_env files in
  let (ast, env) = descatter env ast in
  let (ast, env) =
    List.fold_right (fun file (ast,_) -> Splice.splice ast file)
      (!opt_splice) (ast, env)
  in
  let (ast, env) = rewrite_ast_target "lem" env ast in
  Constraint.save_digests ();
  (ast, env)
