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
    fun_renames : string Bindings.t;
    reg_ref_renames : string Bindings.t;
  }

let lstrip f s =
  let rec idx_from i =
    if i >= String.length s || not (f (String.get s i)) then i else idx_from (i + 1)
  in
  let idx = idx_from 0 in
  if idx >= String.length s then "" else String.sub s idx (String.length s - idx)

let rstrip f s =
  let rec idx_from i =
    if i < 0 || not (f (String.get s i)) then i else idx_from (i - 1)
  in
  let idx = idx_from (String.length s - 1) in
  if idx < 0 then "" else String.sub s 0 (idx + 1)

let isa_name id =
  string_of_id id
  |> String.map (fun c -> if c = '#' then '_' else c)
  |> lstrip (fun c -> c = '_')
  |> rstrip (fun c -> c = '_')

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
  (* Approximate renaming of functions by Lem, with option to manually override *)
  let fun_renames = Bindings.map to_string (optional_bindings (member "fun_renames" arch)) in
  let add_fun_rename (orig_names, fun_renames) id =
    let name = isa_name id in
    let fun_renames = match List.filter (fun n -> name = n) orig_names with
      | names when List.length names > 0 && not (Bindings.mem id fun_renames) ->
         let name' = name ^ string_of_int (List.length names - 1) in
         Bindings.add id name' fun_renames
      | _ -> fun_renames
    in
    (name :: orig_names, fun_renames)
  in
  let fun_renames = snd (List.fold_left add_fun_rename ([], fun_renames) (Analyse_sail.fun_ids ast)) in
  { name = to_string (member "name" arch);
    ast;
    type_env;
    cap_regs;
    privileged_regs = optional_idset (member "privileged_regs" arch);
    conf_regs;
    cap_types;
    fun_infos;
    fun_renames;
    reg_ref_renames = Bindings.map to_string (optional_bindings (member "reg_ref_renames" arch));
  }
