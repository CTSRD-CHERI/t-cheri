open Ast
open Ast_util
open Rewriter

type fun_info =
  { arg_typs : typ list;
    ret_typ : typ;
    effect : effect;
    calls : IdSet.t;
    regs_read : IdSet.t;
    regs_written : IdSet.t;
    trans_regs_read : IdSet.t;
    trans_regs_written : IdSet.t }

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

let add_fun_infos_of_def env fun_infos = function
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
     let regs_written = merge (List.map regs_written_in_exp exps) in
     let trans_regs_read =
       List.map (fun (_, info) -> info.trans_regs_read) (Bindings.bindings calls_infos)
       |> List.fold_left IdSet.union regs_read
     in
     let trans_regs_written =
       List.map (fun (_, info) -> info.trans_regs_written) (Bindings.bindings calls_infos)
       |> List.fold_left IdSet.union regs_written
     in
     let arg_typs, ret_typ, effect = match Type_check.Env.get_val_spec id env with
       | _, Typ_aux (Typ_fn (arg_typs, ret_typ, effect), _) -> arg_typs, ret_typ, effect
       | _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ ("Function " ^ string_of_id id ^ " does not have function type"))
     in
     Bindings.add id { arg_typs; ret_typ; effect; calls; regs_read; regs_written; trans_regs_read; trans_regs_written } fun_infos
  | DEF_internal_mutrec _ ->
     raise (Reporting.err_todo Parse_ast.Unknown "Analysis of mutually recursive functions not implemented")
  | _ -> fun_infos

let fun_ids defs = List.concat (List.map (function DEF_fundef fd -> [id_of_fundef fd] | _ -> []) defs)

let fun_infos_of_defs env defs = List.fold_left (add_fun_infos_of_def env) Bindings.empty defs

let load_files ?mutrecs:(mutrecs=IdSet.empty) files =
  let open Process_file in
  Nl_flow.opt_nl_flow := true;
  Type_check.opt_no_lexp_bounds_check := true;
  Process_file.opt_memo_z3 := true;
  Reporting.opt_warnings := false;
  Initial_check.opt_undefined_gen := true;
  Initial_check.opt_magic_hash := true;
  Type_check.opt_no_effects := true;
  Constant_propagation_mutrec.targets := IdSet.elements mutrecs;
  Util.opt_verbosity := 1;

  let _, ast, env = load_files [] Type_check.initial_env files in
  let ast, env = descatter env ast in
  rewrite_ast_target "lem" env ast
