open Yojson.Basic.Util
open Ast_util
open Arch
open Analyse_sail
open Lemma

let opt_src_dir = ref Filename.current_dir_name
let opt_out_dir = ref Filename.current_dir_name

let options =
  Arg.align [
      ("-src_dir",
       Arg.String (fun dir -> opt_src_dir := dir),
       "<dir> Source directory with Sail files");
      ( "-splice",
        Arg.String (fun s -> Analyse_sail.opt_splice := s :: !Analyse_sail.opt_splice),
        "<filename> add functions from file, replacing existing definitions where necessary");
      ("-out_dir",
       Arg.String (fun dir -> opt_out_dir := dir),
       "<dir> Output directory")
    ]

let usage_msg = "usage: gen_lemmas <arch.json>\n"

(* let thy_name = isa_name ^ "_Gen_Lemmas"
let thy_imports = isa_name ^ "_Instantiation" *)

let has_mem_eff f =
  let open Ast in
  let mem_effs = [BE_rmem; BE_rmemt; BE_wmem; BE_wmv; BE_wmvt; BE_eamem] in
  List.exists (has_effect f.effect) mem_effs

let effectful f = Pretty_print_lem.effectful f.effect

let ids_overlap x y = not (IdSet.disjoint x y)
let reads rs f = ids_overlap rs f.trans_regs_read
let writes rs f = ids_overlap rs f.trans_regs_written
let uses rs f = (reads rs f || writes rs f)

let is_cap_typ isa typ =
  let open Type_check in
  let typ = Env.expand_synonyms isa.type_env typ in
  List.exists (alpha_equivalent isa.type_env typ) isa.cap_types

let base_typ_of isa typ = Type_check.Env.base_typ_of isa.type_env typ

let returns_cap isa f = is_cap_typ isa f.ret_typ
let is_cap_fun isa f = has_mem_eff f || uses isa.cap_regs f

let has_ref_args f = List.exists is_ref_typ f.arg_typs

let mangle_name renames n =
  (try Bindings.find n renames with Not_found -> isa_name n)

let mangle_fun_name arch = mangle_name arch.fun_renames
let mangle_reg_ref arch n = mangle_name arch.reg_ref_renames (append_id n "_ref")

let format_fun_name arch id = mangle_fun_name arch id
let format_fun_args f = String.concat " " (List.mapi (fun i _ -> "arg" ^ string_of_int i) f.arg_typs)
let format_fun_call arch id f = format_fun_name arch id ^ " " ^ format_fun_args f

let apply_lemma_override arch id lemma_type lemma =
  match Bindings.find_opt id arch.lemma_overrides with
  | Some overrides ->
     begin match StringMap.find_opt lemma_type overrides with
       | Some override -> apply_override override lemma
       | None -> lemma
     end
  | None -> lemma

let get_fun_info isa id =
  let f = Bindings.find id isa.fun_infos in
  (f, format_fun_name isa id, format_fun_call isa id f)

let non_cap_exp_lemma isa id : lemma =
  let (f, name, call) = get_fun_info isa id in
  let get_arg_assm i r =
    if (is_ref_typ r && not (is_cap_typ isa (base_typ_of isa r))) then
      ["non_cap_reg arg" ^ string_of_int i]
    else []
  in
  let assms = List.concat (List.mapi get_arg_assm f.arg_typs) in
  let using = (if assms = [] then [] else ["assms"]) in
  { name = "non_cap_exp_" ^ name; attrs = "[non_cap_expI]"; assms;
    stmts = ["non_cap_exp (" ^ call ^ ")"];
    proof = "(unfold " ^ name ^ "_def, non_cap_expI)";
    using; unfolding = [] }
  |> apply_lemma_override isa id "non_cap_exp"

let non_mem_exp_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  { name = "non_mem_exp_" ^ name; attrs = "[non_mem_expI]"; assms = [];
    stmts = ["non_mem_exp (" ^ call ^ ")"];
    proof = "(unfold " ^ name ^ "_def, non_mem_expI)";
    using = []; unfolding = [] }
  |> apply_lemma_override isa id "non_mem_exp"

let no_reg_writes_to_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  (* Restricting attention to capability registers for now *)
  let regs = IdSet.elements (IdSet.inter f.trans_regs_written isa.cap_regs) in
  let reg_names = List.map (fun r -> "''" ^ string_of_id r ^ "''") regs in
  let reg_refs = List.map (mangle_reg_ref isa) regs in
  let reg_defs = List.map (fun n -> n ^ "_def") reg_refs in
  let get_arg_assm i r = if (is_ref_typ r && not (is_cap_typ isa (base_typ_of isa r))) then ["name arg" ^ string_of_int i ^ " \\<notin> Rs"] else [] in
  let assms =
    (if regs = [] then [] else ["Rs \\<subseteq> cap_regs - {" ^ String.concat ", " reg_names ^ "}"]) @
    List.concat (List.mapi get_arg_assm f.arg_typs)
  in
  let using = (if assms = [] then [] else ["assms"]) in
  let simps = if regs = [] then "" else " simp: " ^ String.concat " " reg_defs in
  { name = "no_reg_writes_to_" ^ name; attrs = "[no_reg_writes_toI, simp]"; assms;
    stmts = ["no_reg_writes_to Rs (" ^ call ^ ")"];
    unfolding = [(name ^ "_def"); "bind_assoc"]; using;
    proof = "(no_reg_writes_toI" ^ simps ^ ")" }
  |> apply_lemma_override isa id "no_reg_writes_to"

let return_caps_derivable_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  { name = name ^ "_derivable"; attrs = "[derivable_capsE]";
    assms = ["Run (" ^ call ^ ") t c"; "trace_assm t"];
    stmts = ["c \\<in> derivable_caps (run s t)"];
    unfolding = [(name ^ "_def")]; using = ["assms"];
    proof = "derivable_capsI" }
  |> apply_lemma_override isa id "derivable_caps"

let traces_enabled_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  let cap_regs_read = IdSet.inter isa.cap_regs (IdSet.union f.regs_read (IdSet.diff f.trans_regs_read isa.privileged_regs)) in
  let cap_reg_names = List.map (fun r -> "''" ^ string_of_id r ^ "''") (IdSet.elements cap_regs_read) in
  let cap_assm =
    if ids_overlap cap_regs_read isa.privileged_regs || (writes isa.cap_regs f && not (IdSet.is_empty cap_regs_read)) then
      ["{" ^ String.concat ", " cap_reg_names ^ "} \\<subseteq> accessible_regs s"]
    else []
  in
  let arg_assms =
    if has_mem_eff f || writes isa.cap_regs f then
      List.concat (List.mapi (fun i t -> if is_cap_typ isa t then ["arg" ^ string_of_int i ^ " \\<in> derivable_caps s"] else []) f.arg_typs)
    else []
  in
  let assms = cap_assm @ arg_assms in
  let using = if assms = [] then "" else " assms: assms" in
  { name = "traces_enabled_" ^ name; attrs = "[traces_enabledI]";
    assms; unfolding = [(name ^ "_def"); "bind_assoc"]; using = [];
    stmts = ["traces_enabled (" ^ call ^ ") s"];
    proof = "(traces_enabledI" ^ using ^ ")" }
  |> apply_lemma_override isa id "traces_enabled"

(* let find_strings x m = try StringMap.find x m with Not_found -> StringSet.empty

let trans_calls =
  let add_calls cs (f : fun_info) = StringMap.add f.name (StringSet.fold (fun c cs' -> StringSet.union (find_strings c cs) cs') f.calls f.calls) cs in
  List.fold_left add_calls StringMap.empty fun_infos

let funs_called_by funs =
  let add_funs_called fs (f : fun_info) = StringSet.union fs (find_strings f.name trans_calls) in
  List.fold_left add_funs_called StringSet.empty funs

let regs_used =
  let add_used_regs regs f =
    StringSet.union regs (StringSet.union f.regs_read f.regs_written)
  in
  StringSet.diff (List.fold_left add_used_regs StringSet.empty fun_infos) conf_regs *)

let non_cap_regs_lemma isa : lemma =
  let regs = State.find_registers isa.ast |> List.map snd |> IdSet.of_list in
  let non_cap_regs = IdSet.elements (IdSet.diff regs (IdSet.union isa.cap_regs isa.privileged_regs)) in
  let stmts = List.map (fun r -> "non_cap_reg " ^ mangle_reg_ref isa r) non_cap_regs in
  { name = "non_cap_regsI"; attrs = "[intro, simp]";
    assms = []; unfolding = []; using = []; stmts;
    proof = "(auto simp: non_cap_reg_def register_defs)" }

let write_cap_regs_lemma isa =
  let stmt r = "traces_enabled (write_reg " ^ mangle_reg_ref isa r ^ " c) s" in
  let stmts = List.map stmt (IdSet.elements isa.cap_regs) in
  { name = "traces_enabled_write_cap_regs"; attrs = "[traces_enabledI]";
    assms = ["c \\<in> derivable_caps s"]; unfolding = []; using = ["assms"];
    stmts;
    proof = "(intro traces_enabled_write_reg; auto simp: register_defs derivable_caps_def)+" }

let read_cap_regs_lemma isa =
  let stmt r =
    let assms = if IdSet.mem r isa.privileged_regs then "system_reg_access s \\<or> has_ex \\<Longrightarrow> " else "" in
    assms ^ "traces_enabled (read_reg " ^ mangle_reg_ref isa r ^ ") s"
  in
  let stmts = List.map stmt (IdSet.elements isa.cap_regs) in
  { name = "traces_enabled_read_cap_regs"; attrs = "[traces_enabledI]";
    assms = []; unfolding = []; using = []; stmts;
    proof = "(intro traces_enabled_read_reg; auto simp: register_defs)+" }

let read_cap_regs_derivable_lemma isa =
  let stmt r =
    "\\<And>t c s. Run (read_reg " ^ mangle_reg_ref isa r ^ ") t c" ^
    " \\<Longrightarrow> trace_assm t" ^
    " \\<Longrightarrow> {''" ^ string_of_id r ^ "''} \\<subseteq> accessible_regs s" ^
    " \\<Longrightarrow> c \\<in> derivable_caps (run s t)"
  in
  let stmts = List.map stmt (IdSet.elements isa.cap_regs) in
  { name = "read_cap_regs_derivable"; attrs = "[derivable_capsE]";
    assms = []; unfolding = []; using = []; stmts;
    proof = "(auto simp: derivable_caps_def elim!: Run_read_regE intro!: derivable.Copy)" }

let output_line chan l =
  output_string chan l;
  output_string chan "\n"

let funs isa = fun_ids isa.ast
let filter_funs isa p = List.filter (fun id -> p id (Bindings.find id isa.fun_infos)) (funs isa)

let output_cap_lemmas chan (isa : isa) =
  output_line chan  "theory CHERI_Cap_Lemmas";
  output_line chan  "imports CHERI_Instantiation";
  output_line chan  "begin";
  output_line chan  "";
  output_line chan ("context " ^ isa.name ^ "_Axiom_Automaton");
  output_line chan  "begin";
  output_line chan  "";

  output_line chan (format_lemma (non_cap_regs_lemma isa));
  output_line chan  "lemmas non_cap_exp_rw_non_cap_reg[non_cap_expI] =";
  output_line chan  "  non_cap_regsI[THEN non_cap_exp_read_non_cap_reg]";
  output_line chan  "  non_cap_regsI[THEN non_cap_exp_write_non_cap_reg]";
  output_line chan  "";

  filter_funs isa (fun id f -> not (is_cap_fun isa f) && effectful f)
    |> List.map (non_cap_exp_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "";
  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let output_cap_props chan (isa : isa) =
  output_line chan  "theory CHERI_Cap_Properties";
  output_line chan  "imports CHERI_Cap_Lemmas";
  output_line chan  "begin";
  output_line chan  "";

  output_line chan ("context " ^ isa.name ^ "_Write_Cap_Automaton");
  output_line chan  "begin";
  output_line chan  "";

  output_line chan (format_lemma (write_cap_regs_lemma isa));
  output_line chan (format_lemma (read_cap_regs_lemma isa));

  output_line chan  "";

  output_line chan  "lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]\n";
  output_line chan  "";

  filter_funs isa (fun id f -> is_cap_fun isa f)
    |> List.map (traces_enabled_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let output_mem_props chan (isa : isa) =
  output_line chan  "theory CHERI_Mem_Properties";
  output_line chan  "imports CHERI_Cap_Lemmas";
  output_line chan  "begin";
  output_line chan  "";

  output_line chan ("context " ^ isa.name ^ "_Axiom_Automaton");
  output_line chan  "begin";
  output_line chan  "";

  filter_funs isa (fun id f -> (is_cap_fun isa f || has_ref_args f) && not (has_mem_eff f))
    |> List.map (non_mem_exp_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "end";
  output_line chan  "";
  output_line chan ("context " ^ isa.name ^ "_Mem_Automaton");
  output_line chan  "begin";
  output_line chan  "";

  output_line chan  "lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]\n";
  output_line chan  "lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]\n";
  output_line chan  "";

  filter_funs isa (fun id f -> has_mem_eff f)
    |> List.map (traces_enabled_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let process_isa file =
  let isa = load_isa file !opt_src_dir in
  let out_file name = Filename.concat !opt_out_dir name in

  let chan = open_out (out_file "CHERI_Cap_Lemmas.thy") in
  output_cap_lemmas chan isa;
  flush chan;
  close_out chan;

  let chan = open_out (out_file "CHERI_Cap_Properties.thy") in
  output_cap_props chan isa;
  flush chan;
  close_out chan;

  let chan = open_out (out_file "CHERI_Mem_Properties.thy") in
  output_mem_props chan isa;
  flush chan;
  close_out chan

let main () =
  let opt_file_arguments = ref [] in
  Arg.parse options (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg;
  match !opt_file_arguments with
  | [file] -> process_isa file
  | _ -> Arg.usage options usage_msg

let () =
  try main () with
  | Reporting.Fatal_error e ->
     Reporting.print_error e;
     exit 1
