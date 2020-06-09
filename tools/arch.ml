open Ast
open Ast_util
open Lemma
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
    lemma_overrides : lemma_override StringMap.t Bindings.t;
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

let load_isa file src_dir =
  let to_id json = mk_id (to_string json) in
  let to_idset json = IdSet.of_list (convert_each to_id json) in
  let optional_idset json = Util.option_default IdSet.empty (to_option to_idset json) in
  let add_assoc b (key, value) = Bindings.add (mk_id key) value b in
  let to_bindings json = List.fold_left add_assoc Bindings.empty (to_assoc json) in
  let optional_bindings json = Util.option_default Bindings.empty (to_option to_bindings json) in
  let add_sassoc b (key, value) = StringMap.add key value b in
  let to_typ json = Initial_check.typ_of_string (to_string json) in
  let to_string_list json = convert_each to_string json in
  let to_override json =
    { name_override = to_option to_string (member "name" json);
      attrs_override = to_option to_string (member "attrs" json);
      assms_override = to_option to_string_list (member "assms" json);
      stmts_override = to_option to_string_list (member "stmts" json);
      using_override = to_option to_string_list (member "using" json);
      unfolding_override = to_option to_string_list (member "unfolding" json);
      proof_override = to_option to_string (member "proof" json);
    }
  in

  let arch = Yojson.Basic.from_file file in
  let files =
    convert_each to_string (member "files" arch)
    |> List.map (Filename.concat src_dir)
  in
  let mutrecs = optional_idset (member "mutrecs" arch) in
  let (Defs ast, type_env) = Analyse_sail.load_files ~mutrecs files in
  let (Defs ast) = match to_option to_assoc (member "slice" arch) with
    | Some assoc ->
       let module NodeSet = Set.Make(Slice.Node) in
       let module G = Graph.Make(Slice.Node) in
       let to_node json = Slice.Function (mk_id (to_string json)) in
       let to_nodeset = function
         | Some json -> NodeSet.of_list (convert_each to_node json)
         | None -> NodeSet.empty
       in
       let roots = to_nodeset (List.assoc_opt "roots" assoc) in
       let cuts = to_nodeset (List.assoc_opt "cuts" assoc) in
       let g = G.prune roots cuts (Slice.graph_of_ast (Defs ast)) in
       Slice.filter_ast cuts g (Defs ast)
    | None -> Defs ast
  in
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
  let add_overrides (fun_renames, lemma_overrides) (f, overrides) =
    let (renames, overrides) = List.partition (fun (name, _) -> name = "name") (to_assoc overrides) in
    let fun_renames = match List.rev renames with
      | [] -> fun_renames
      | (_, name') :: _ -> Bindings.add (mk_id f) (to_string name') fun_renames
    in
    let lemma_overrides = match overrides with
      | [] -> lemma_overrides
      | overrides ->
         let overrides_map = List.fold_left add_sassoc StringMap.empty overrides in
         Bindings.add (mk_id f) (StringMap.map to_override overrides_map) lemma_overrides
    in
    (fun_renames, lemma_overrides)
  in
  let (fun_renames, lemma_overrides) = match to_option to_assoc (member "overrides" arch) with
    | Some assoc ->
       List.fold_left add_overrides (Bindings.empty, Bindings.empty) assoc
    | None -> (Bindings.empty, Bindings.empty)
  in
  (* Approximate renaming of functions by Lem (unless manually overridden) *)
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
    lemma_overrides;
    reg_ref_renames = Bindings.map to_string (optional_bindings (member "reg_ref_renames" arch));
  }
