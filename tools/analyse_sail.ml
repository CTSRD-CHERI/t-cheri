open Ast
open Ast_util
open Rewriter

let opt_splice = ref ([]:string list)

type fun_info =
  { typquant : typquant;
    arg_typs : typ list;
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

let exception_funs defs = List.fold_left add_exception_fun IdSet.empty defs

let add_fun_infos_of_def env exception_funs fun_infos = function
  | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _) as fd) ->
     let id = id_of_fundef fd in
     let exp_of_pexp pexp =
       let (_, _, exp, _) = destruct_pexp pexp in
       exp
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
     Bindings.add id
       {
         typquant; arg_typs; ret_typ; effect; calls; regs_read; regs_read_no_exc; regs_written; regs_written_no_exc;
         trans_calls; trans_regs_read; trans_regs_read_no_exc; trans_regs_written; trans_regs_written_no_exc
       }
       fun_infos
  | DEF_internal_mutrec _ ->
     raise (Reporting.err_todo Parse_ast.Unknown "Analysis of mutually recursive functions not implemented")
  | _ -> fun_infos

let fun_ids defs = List.concat (List.map (function DEF_fundef fd -> [id_of_fundef fd] | _ -> []) defs)

let fun_infos_of_defs env defs =
  let exc_funs = exception_funs defs in
  List.fold_left (add_fun_infos_of_def env exc_funs) Bindings.empty defs

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

  let _, ast, env = load_files [] Type_check.initial_env files in
  let ast, env = descatter env ast in
  let ast, env =
    List.fold_right (fun file (ast,_) -> Splice.splice ast file)
      (!opt_splice) (ast, env)
  in
  rewrite_ast_target "lem" env ast
