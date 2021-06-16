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
let mk_conj a b = mk_exp (E_app (mk_id "and_bool_precond_no_flow", [a; b]))
let mk_disj a b = mk_exp (E_app (mk_id "or_bool_precond_no_flow", [a; b]))
let mk_not a = mk_exp (E_app (mk_id "not_bool", [a]))

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

let rec pat_to_id_opt = function
  | P_aux (P_id id, _) -> Some id
  | P_aux (P_typ (_, p), _) -> pat_to_id_opt p
  | _ -> None

let plet_id_worker = function
  | (p, (E_aux (E_id id2, _) as v), body) -> begin match pat_to_id_opt p with
    | Some id -> unaux_exp (subst id v body)
    | None -> E_internal_plet (p, v, body)
  end
  | (p, exp, body) -> E_internal_plet (p, exp, body)

let let_id_worker = function
  | ((LB_aux (LB_val (p, (E_aux (E_id id2, _) as v)), _) as lb), body) ->
  begin match pat_to_id_opt p with
    | Some id -> unaux_exp (subst id v body)
    | None -> E_let (lb, body)
  end
  | (lb, body) -> E_let (lb, body)

let field_worker field_simps (x, id) = match Bindings.find_opt id field_simps with
  | None -> E_field (x, id)
  | Some (v_id, _) -> E_id v_id

let precond_simp = fold_exp { id_exp_alg with
    e_case = case_to_if_worker;
(*
    e_app = (fun (id, args) -> vector_eq_lit_worker id args (E_app (id, args)));
    e_app_infix = (fun (lhs, id, rhs) -> vector_eq_lit_worker id
        [lhs; rhs] (E_app_infix (lhs, id, rhs)));
*)
    e_let = let_id_worker;
    e_internal_plet = plet_id_worker
}

(* precondition information. notes which functions have preconditions,
   and for those that do, which arguments to the function are relevant.
   also notes which function preconditions have been discovered to be
   trivial/tautological.
*)
type preconds = {
    funs : (bool list * (id * typ) list) Bindings.t;
    triv : IdSet.t
}

let precond_suffix = "_precondition"
let precond_name id = append_id id precond_suffix

let adjust_args : (bool list -> 'a list -> 'a list) = fun present args -> List.fold_right2
    (fun x p xs -> if p then x :: xs else xs) args present []

let get_precond_args preconds id args = match Bindings.find_opt id preconds.funs with
  | None -> None
  | Some (present, regs) -> Some (precond_name id, regs, adjust_args present args)

let preconds_verbose = true
let log_msg s = if preconds_verbose then prerr_endline s else ()

let drop_tannot exp = map_exp_annot (fun (l, _) -> (l, ())) exp

let get_precond_app preconds id args = if IdSet.mem id preconds.triv
  then []
  else
  match get_precond_args preconds id (List.map drop_tannot args) with
  | None -> []
  | Some (id2, regs, args2) ->
    let extras = List.map (fun (id, _) -> mk_exp (E_id id)) regs in
    let args3 = match extras @ args2 with
      | [] -> [mk_lit_exp L_unit]
      | xs -> xs
    in
    log_msg ("including precond from " ^ string_of_id id2);
    [mk_exp (E_app (id2, args3))]

let let_rhs_triv exp =
  fold_exp { (pure_exp_alg false (&&)) with
    e_id = (fun _ -> true);
    e_lit = (fun _ -> true)
  } exp

let filter_for_let fun_id ids (p, body) assertions =
  let xs = List.filter (ids_not_present ids) assertions in
  let n = List.length assertions - List.length xs in
  if n > 0
  then prerr_endline ("dropped " ^ string_of_int n ^
    " assertions (" ^
    Util.string_of_list ", " string_of_id (IdSet.elements ids) ^
    ": " ^ string_of_pat p ^
    " = " ^ string_of_exp body ^ ") in " ^
    string_of_id fun_id)
  else ();
  xs

let apply_let_bind fun_id p body assertions = match p with
  | P_aux (P_id id, _) -> if let_rhs_triv body
    then List.map (subst id (drop_tannot body)) assertions
    else filter_for_let fun_id (pat_ids p) (p, body) assertions
  | _ -> filter_for_let fun_id (pat_ids p) (p, body) assertions

let rec scan_assertions_aux nm preconds x =
  let scan = scan_assertions nm preconds in
  match x with
  | E_block es -> List.concat (List.map scan es)
  | E_assert (e, msg) -> [drop_tannot e]
  | E_if (c, x, y) ->
    let c2 = drop_tannot c in
    let x_assns = match scan x with
      | [] -> []
      | xs -> [mk_disj (mk_not c2) (mk_conjs xs)]
    in
    let y_assns = match scan y with
      | [] -> []
      | xs -> [mk_disj c2 (mk_conjs xs)]
    in
    x_assns @ y_assns
  | E_cast (_, e) -> scan e
  | E_throw e -> if throw_is_failure e then [false_exp] else []
  | E_let (LB_aux (LB_val (p, e1), _), e2) ->
        scan e1 @ apply_let_bind nm p e1 (scan e2)
  | E_internal_plet (p, e1, e2) ->
        scan e1 @ apply_let_bind nm p e1 (scan e2)
  | E_app (id, args) -> get_precond_app preconds id args
  | E_app_infix (lhs, id, rhs) -> get_precond_app preconds id [lhs; rhs]
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

let find_val_spec_typ id defs =
  match List.find_opt (fun d -> IdSet.mem id (val_spec_ids [d])) defs with
  | Some (DEF_spec (VS_aux (VS_val_spec (tysch, _, _, _), _))) ->
  let TypSchm_aux (TypSchm_ts (q, ty), _) = tysch in
  if List.length (quant_items q) > 0
  then raise (Reporting.err_general Parse_ast.Unknown
    ("find_val_spec_typ: quantified typ of " ^ string_of_id id))
  else ();
  ty
  | _ -> raise (Reporting.err_general Parse_ast.Unknown
    ("find_val_spec_typ: no spec for " ^ string_of_id id))

let precond_smt_check env ast fn_name =
  try
  let pname = precond_name fn_name in
  let ast = Slice.filter_ast_ids (IdSet.singleton pname) IdSet.empty ast in
  let (ast, env) = Process_file.rewrite_ast_target "c" env ast in
  let ty = find_val_spec_typ pname ast.defs in
  let ty_args = match ty with
    | Typ_aux (Typ_fn (args, _, _), _) -> args
    | _ -> raise (Reporting.err_general Parse_ast.Unknown
        ("precond_smt_check: not fun type: " ^ string_of_id fn_name))
  in
  let (jdefs, jctxt, smt_ctxt) = Jib_smt.compile env ast in
  let file_name = "/tmp/test_" ^ string_of_id pname ^ ".smt2" in
  Jib_smt.smt_query_to_file file_name jctxt smt_ctxt pname (ty_args, mk_id_typ (mk_id "bool"))
    "property" (Property.Q_all Property.Return) jdefs;
  let smt_in = Unix.open_process_in ("z3 -smt2 -T:2 " ^ file_name) in
  let res = smt_result smt_in in
  let _ = Unix.close_process_in smt_in in
  prerr_endline (if res then "smt: precond trivial" else "smt: precond non-trivial");
  res
  with Failure _ ->
    prerr_endline ("smt conversion failed, carrying on"); false

let pat_to_id p = match pat_to_id_opt p with
  | Some id -> id
  | _ -> raise (Reporting.err_general (pat_loc p) ("pat not id: " ^ string_of_pat p))

let no_binders exp = fold_exp
  { (pure_exp_alg true (&&)) with
    e_for = (fun _ -> false) ;
    pat_alg = { (pure_pat_alg true (&&)) with p_id = (fun _ -> false) }
  } exp

let simplify_binding regs_read (p, body) =
  let (args, is_unit) = match p with
    | P_aux (P_tup xs, _) -> (List.map pat_to_id xs, false)
    | P_aux (P_id id, _) -> ([id], false)
    | P_aux (P_lit (L_aux (L_unit, _)), _) -> ([], true)
    | P_aux (_, (l, _)) ->
      raise (Reporting.err_general l ("simplify_binding: fundef pattern: " ^ string_of_pat p))
  in
  let args_present = List.map (fun id -> (id, ids_present (IdSet.singleton id) body)) args in
  let present_arg_ids = List.filter snd args_present |> List.map fst in
  let arg_ids = regs_read @ present_arg_ids in
  let args = List.map (fun id -> mk_pat (P_id id)) arg_ids in
  let p2 = match args with
    | [] -> mk_pat P_wild
    | [p] -> p
    | ps -> mk_pat (P_tup ps)
  in
  (p2, arg_ids, List.map snd args_present @ (if is_unit then [false] else []))

let get_reg_typ env id =
  if Type_check.Env.is_register id env
  then let (_, _, typ) = Type_check.Env.get_register id env in typ
  else raise (Reporting.err_general Parse_ast.Unknown "get_reg_typ: not reg")

let type_check_assn_def env id p assn =
    let (q, typ) = Type_check.Env.get_val_spec_orig id env in
    let q_params = quant_items q in
    if List.length q_params > 0
    then
        (prerr_endline ("dropping precondition for " ^ string_of_id id ^
            ": type quantifiers: " ^
            Util.string_of_list ", " string_of_quant_item q_params);
            failwith "type_check_assn_def")
    else
    let ty_args = match unaux_typ typ with
        | Typ_fn (ty_args, _, _) -> ty_args
        | _ -> raise (Reporting.err_general Parse_ast.Unknown
                ("unexpected non-function type of " ^ string_of_id id))
    in
    let p2 = map_pat_annot (fun _ -> no_annot) p in
    let (_, arg_ids, adj_args) = simplify_binding [] (p2, assn) in
    let ty_args2 = adjust_args adj_args ty_args in
    let bound_env = List.fold_right2 (fun id ty -> Type_check.Env.add_local id (Immutable, ty))
        arg_ids ty_args2 env in
    let check_assn = try Type_check.check_exp bound_env assn bool_typ
    with Type_check.Type_error (_, l, err) ->
        raise (Reporting.err_typ l (Type_error.string_of_type_error err))
    in
    let regs_read = regs_read_in_exp check_assn |> IdSet.elements in
    let typed_regs = List.map (fun r -> (r, get_reg_typ env r)) regs_read in
    let reg_renames = List.map (fun id -> (id, append_id id "_parameter")) regs_read in
    let assn_rename = List.fold_right (fun (id, id2) -> subst id (mk_exp (E_id id2)))
        reg_renames assn in
    let (p3, _, adj_args) = simplify_binding (List.map snd reg_renames) (p2, assn) in
    let pid = precond_name id in
    let fund = mk_fundef [mk_funcl pid p3 assn_rename] in
    let ty_args3 = match List.map snd typed_regs @ ty_args2 with
        | [] -> [unit_typ]
        | tys -> tys
    in
    let typ2 = mk_typ (Typ_fn (ty_args3, bool_typ, no_effect)) in
    let spec = mk_val_spec (VS_val_spec (mk_typschm q typ2, pid, [], false)) in
    let (defs, env2) = Type_error.check_defs env [spec; fund] in
    ((adj_args, typed_regs), defs, env2)

let add_funcl_assertions ast data = function
  | FCL_aux (FCL_Funcl (id, Pat_aux (Pat_exp (p, body), _)), (l, _)) ->
    log_msg ("scanning " ^ string_of_id id ^ " for preconditions");
    let (env, precond_defs, preconds) = data in
    let body2 = precond_simp body in
    log_msg ("converted body");
    begin try match scan_assertions id preconds body2 with
    | [] -> data
    | assns ->
        prerr_endline ("got a precondition for " ^ (string_of_id id));
        let assn = mk_conjs assns in
        let (arg_info, defs, env2) = type_check_assn_def env id p assn in
        let preconds2 = { preconds with funs = Bindings.add id arg_info preconds.funs } in
        let precond_defs2 = precond_defs @ defs in
        let triv = precond_smt_check env2 (append_ast_defs ast precond_defs2) id in
        let preconds3 = if triv then { preconds2 with triv = IdSet.add id preconds2.triv }
            else preconds2 in
       (env2, precond_defs2, preconds3)
    with Failure _ -> data
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

let bool_ops =
  let x = mk_id "x" in
  let y = mk_id "y" in
  let xy_pat = mk_pat (P_tup [mk_pat (P_id x); mk_pat (P_id y)]) in
  let ty = mk_typ (Typ_fn ([bool_typ; bool_typ], bool_typ, no_effect)) in
  let tysch = mk_typschm (mk_typquant []) ty in
  let or_simple = mk_id "or_bool_precond_no_flow" in
  let and_simple = mk_id "and_bool_precond_no_flow" in
  [
    mk_val_spec (VS_val_spec (tysch, or_simple, [], false));
    mk_fundef [mk_funcl or_simple xy_pat
        (mk_exp (E_app (mk_id "or_bool", [mk_exp (E_id x); mk_exp (E_id y)])))];
    mk_val_spec (VS_val_spec (tysch, and_simple, [], false));
    mk_fundef [mk_funcl and_simple xy_pat
        (mk_exp (E_app (mk_id "and_bool", [mk_exp (E_id x); mk_exp (E_id y)])))]]

let add_unique_fields l fs (typ, id) = Bindings.update id
  (fun x -> match x with
    | None -> Some [(l, typ)]
    | Some xs -> Some ((l, typ) :: xs)
  ) fs

let get_preconds env ast =
  Reporting.opt_warnings := true;
  prerr_endline ("getting preconds for " ^ (string_of_int (List.length ast.defs)) ^ " ast elems");
  let (bool_defs, env) = Type_error.check_defs env bool_ops in
  let preconds = {funs = Bindings.empty; triv = IdSet.empty} in
  let (env, precond_defs, preconds) = List.fold_left (add_fun_assertions ast)
        (env, bool_defs, preconds) ast.defs in
  prerr_endline ("got " ^ string_of_int (List.length precond_defs) ^ " precond ast elems");
  let ids_set typed_ids = List.fold_right (fun (id, _) -> IdSet.add id) typed_ids IdSet.empty in
  let regs = Bindings.fold (fun _ (_, regs) -> IdSet.union (ids_set regs))
    preconds.funs IdSet.empty in
  prerr_endline ("registers used in preconds: [" ^ Util.string_of_list ", "
        string_of_id (IdSet.elements regs) ^ "]");
  (env, precond_defs, preconds, regs)

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
