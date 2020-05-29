open Ast
open Ast_util
open Yojson.Basic.Util

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type isa =
  { name : string;
    ast : Type_check.tannot def list;
    type_env : Type_check.Env.t;
    cap_regs : IdSet.t;
    privileged_regs : IdSet.t;
    conf_regs : IdSet.t;
    cap_types : typ list;
    fun_infos : Analyse_sail.fun_info Bindings.t;
    fun_renames : id Bindings.t;
    reg_ref_renames : id Bindings.t;
  }

let load_isa file =
  let to_id json = mk_id (to_string json) in
  let to_idset json = IdSet.of_list (convert_each to_id json) in
  let optional_idset json = Util.option_default IdSet.empty (to_option to_idset json) in
  let add_assoc b (key, value) = Bindings.add (mk_id key) value b in
  let to_bindings json = List.fold_left add_assoc Bindings.empty (to_assoc json) in
  let optional_bindings json = Util.option_default Bindings.empty (to_option to_bindings json) in
  let to_typ json = Initial_check.typ_of_string (to_string json) in

  let arch = Yojson.Basic.from_file file in
  let files = convert_each to_string (member "files" arch) in
  let mutrecs = optional_idset (member "mutrecs" arch) in
  let (Defs ast, type_env) = Analyse_sail.load_files ~mutrecs files in
  let fun_infos = Analyse_sail.fun_infos_of_defs type_env ast in
  let cap_types =
    convert_each to_typ (member "cap_typs" arch)
    |> List.map (Type_check.Env.expand_synonyms type_env)
  in
  let add_conf_reg rs = function
    | DEF_reg_dec (DEC_aux (DEC_config (id, _, _), _)) -> IdSet.add id rs
    | _ -> rs
  in
  let conf_regs = List.fold_left add_conf_reg IdSet.empty ast in
  let cap_regs = match to_option to_idset (member "cap_regs" arch) with
    | Some cap_regs -> cap_regs
    | None ->
       let is_cap_reg (typ, id) =
         let typ = Type_check.Env.expand_synonyms type_env typ in
         List.exists (Type_check.alpha_equivalent type_env typ) cap_types
       in
       State.find_registers ast |> List.filter is_cap_reg |> List.map snd |> IdSet.of_list
  in
  { name = to_string (member "name" arch);
    ast;
    type_env;
    cap_regs;
    privileged_regs = optional_idset (member "privileged_regs" arch);
    conf_regs;
    cap_types;
    fun_infos;
    fun_renames = Bindings.map to_id (optional_bindings (member "fun_renames" arch));
    reg_ref_renames = Bindings.map to_id (optional_bindings (member "reg_ref_names" arch));
  }
