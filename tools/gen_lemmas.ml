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
let effectful_funs isa =
  Bindings.filter (fun _ f -> effectful f) isa.fun_infos
  |> Bindings.bindings |> List.map fst |> IdSet.of_list

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
let cap_funs isa =
  Bindings.filter (fun _ f -> is_cap_fun isa f) isa.fun_infos
  |> Bindings.bindings |> List.map fst |> IdSet.of_list

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

let no_reg_writes_to_lemma no_exc isa id =
  let (f, name, call) = get_fun_info isa id in
  (* Restricting attention to special capability registers for now *)
  let regs_written = if no_exc then f.trans_regs_written_no_exc else f.trans_regs_written in
  let regs = IdSet.elements (IdSet.diff (write_checked_regs isa) regs_written) in
  let reg_names = List.map (fun r -> "''" ^ string_of_id r ^ "''") regs in
  (* let get_arg_assm i r = if (is_ref_typ r && not (is_cap_typ isa (base_typ_of isa r))) then ["name arg" ^ string_of_int i ^ " \\<notin> Rs"] else [] in *)
  let assm =
    "Rs \\<subseteq> {" ^ String.concat ", " reg_names ^ "}"
    (* @ List.concat (List.mapi get_arg_assm f.arg_typs) *)
  in
  let simps = if regs = [] then "" else " simp: register_defs" in
  let exc_prefix = if no_exc then "runs_" else "" in
  { name = exc_prefix ^ "no_reg_writes_to_" ^ name;
    attrs = "[" ^ exc_prefix ^ "no_reg_writes_toI, simp]"; assms = [];
    stmts = [assm ^ " \\<Longrightarrow> " ^ exc_prefix ^ "no_reg_writes_to Rs (" ^ call ^ ")"];
    unfolding = []; using = [];
    proof = "(unfold " ^ name ^ "_def bind_assoc, no_reg_writes_toI" ^ simps ^ ")" }
  |> apply_lemma_override isa id (exc_prefix ^ "no_reg_writes_to")

(* We (currently) only need register write footprints of functions that have
   some capability effects and are called in a block before reads of specific
   registers *)

type footprint_requirements = {
  needed_footprints : IdSet.t;
  called_cap_funs : IdSet.t;
  checked_reads : IdSet.t;
}

let no_requirements = {
  needed_footprints = IdSet.empty; called_cap_funs = IdSet.empty; checked_reads = IdSet.empty
}

let join_requirements r1 r2 = {
  needed_footprints = IdSet.union r1.needed_footprints r2.needed_footprints;
  called_cap_funs = IdSet.union r1.called_cap_funs r2.called_cap_funs;
  checked_reads = IdSet.union r1.checked_reads r2.checked_reads
}

let fun_requirements isa id =
  if Bindings.mem id isa.fun_infos then
    let (f, _, _) = get_fun_info isa id in
    { needed_footprints = IdSet.empty;
      called_cap_funs = if is_cap_fun isa f then IdSet.singleton id else IdSet.empty;
      checked_reads = IdSet.inter (write_checked_regs isa) f.trans_regs_read }
  else no_requirements

let reg_requirements isa id =
  { no_requirements with checked_reads = IdSet.inter (write_checked_regs isa) (IdSet.singleton id) }

let check_requirements left right =
  let needed_footprints =
    if IdSet.is_empty right.checked_reads then
      IdSet.empty
    else
      left.called_cap_funs
  in
  let r = join_requirements left right in
  { r with needed_footprints = IdSet.union r.needed_footprints needed_footprints }

let requirements_alg isa =
  { (Rewriter.pure_exp_alg no_requirements join_requirements) with
    e_id = reg_requirements isa;
    e_app = (fun (id, rs) -> List.fold_left join_requirements (fun_requirements isa id) rs);
    e_app_infix = (fun (r1, id, r2) -> List.fold_left join_requirements (fun_requirements isa id) [r1; r2]);
    lEXP_memory = (fun (id, rs) -> List.fold_left join_requirements (fun_requirements isa id) rs);
    e_block = (fun rs -> List.fold_right check_requirements rs no_requirements);
    e_let = (fun (r1, r2) -> check_requirements r1 r2);
    e_internal_plet = (fun (r1, r2, r3) -> List.fold_right check_requirements [r1; r2; r3] no_requirements);
    pat_when = (fun (r1, r2, r3) -> List.fold_right check_requirements [r1; r2; r3] no_requirements); }

let exp_requirements isa = Rewriter.fold_exp (requirements_alg isa)
let pexp_requirements isa = Rewriter.fold_pexp (requirements_alg isa)
let funcl_requirements isa = function
  | Ast.FCL_aux (Ast.FCL_Funcl (_, funcl), _) -> pexp_requirements isa funcl

let add_needed_footprints isa needed_funs = function
  | Ast.DEF_fundef (Ast.FD_aux (Ast.FD_function (_, _, _, funcls), _)) ->
     let rs = List.map (funcl_requirements isa) funcls in
     let r = List.fold_left join_requirements no_requirements rs in
     IdSet.union needed_funs r.needed_footprints
  | _ -> needed_funs

let needed_footprints isa =
  let ids = List.fold_left (add_needed_footprints isa) IdSet.empty isa.ast in
  (* Add dependencies *)
  let nodes = List.map (fun id -> Slice.Function id) (IdSet.elements ids) in
  let module NodeSet = Set.Make(Slice.Node) in
  let module G = Graph.Make(Slice.Node) in
  let g = Slice.graph_of_ast (Ast.Defs isa.ast) in
  let nodes' = G.reachable (NodeSet.of_list nodes) NodeSet.empty g in
  let ids_of_node = function | Slice.Function id -> [id] | _ -> [] in
  let ids' = List.concat (List.map ids_of_node (NodeSet.elements nodes')) in
  IdSet.union ids (IdSet.inter (IdSet.of_list ids') (effectful_funs isa))

let return_caps_derivable_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  let cap_regs_read = IdSet.inter (special_regs isa) f.trans_regs_read_no_exc in
  let cap_reg_names = List.map (fun r -> "''" ^ string_of_id r ^ "''") (IdSet.elements cap_regs_read) in
  let get_arg_assm i r = if (is_cap_typ isa (base_typ_of isa r)) then ["arg" ^ string_of_int i ^ " \\<in> derivable_caps s \\<Longrightarrow> "] else [] in
  let arg_assm = String.concat "" (List.concat (List.mapi get_arg_assm f.arg_typs)) in
  let access_assm =
    if IdSet.is_empty cap_regs_read then "" else
    ("{" ^ String.concat ", " cap_reg_names ^ "} \\<subseteq> accessible_regs s \\<Longrightarrow> ")
  in
  let next_state = if is_cap_fun isa f then "(run s t)" else "s" in
  { name = name ^ "_derivable"; attrs = "[derivable_capsE]";
    assms = [];
    stmts = ["Run (" ^ call ^ ") t c \\<Longrightarrow> " ^ arg_assm ^ access_assm ^ "c \\<in> derivable_caps " ^ next_state];
    unfolding = []; using = [];
    proof = "(unfold " ^ name ^ "_def, derivable_capsI)" }
  |> apply_lemma_override isa id "derivable_caps"

let traces_enabled_lemma mem isa id =
  let (f, name, call) = get_fun_info isa id in
  let cap_regs_read = IdSet.inter (special_regs isa) f.trans_regs_read_no_exc in
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
  |> apply_lemma_override isa id (if mem then "traces_enabled_mem" else "traces_enabled")

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
    (if IdSet.mem r (special_regs isa) then " \\<Longrightarrow> {''" ^ string_of_id r ^ "''} \\<subseteq> accessible_regs s" else "") ^
    " \\<Longrightarrow> c \\<in> derivable_caps (run s t)"
  in
  let stmts = List.map stmt (IdSet.elements isa.cap_regs) in
  { name = "read_cap_regs_derivable"; attrs = "[derivable_capsE]";
    assms = []; unfolding = []; using = []; stmts;
    proof = "(derivable_capsI elim: read_reg_derivable simp: register_defs)+" }

let exp_fails_lemma isa id =
  let (f, name, call) = get_fun_info isa id in
  { name = "exp_fails_" ^ name; attrs = "[simp]";
    assms = []; unfolding = [(name ^ "_def"); "bind_assoc"]; using = [];
    stmts = ["exp_fails (" ^ call ^ ")"];
    proof = "(auto elim!: Run_bindE Run_ifE Run_letE)" }
  |> apply_lemma_override isa id ("exp_fails")

let output_line chan l =
  output_string chan l;
  output_string chan "\n"

let funs isa = List.filter (fun id -> not (IdSet.mem id isa.skip_funs)) (fun_ids isa.ast)
let filter_funs isa p = List.filter (fun id -> p id (Bindings.find id isa.fun_infos)) (funs isa)

let output_cap_lemmas chan (isa : isa) =
  let exc_funs = exception_funs (isa.ast) in
  let needed_fps = needed_footprints isa in
  output_line chan  "theory CHERI_Gen_Lemmas";
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
  output_line chan  (format_lemma (read_cap_regs_derivable_lemma isa));
  output_line chan  "";

  filter_funs isa (fun id f -> IdSet.mem id exc_funs && effectful f)
    |> List.map (exp_fails_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "";

  filter_funs isa (fun id f -> not (IdSet.subset (write_checked_regs isa) f.trans_regs_written) && IdSet.mem id needed_fps)
    |> List.map (no_reg_writes_to_lemma false isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "";

  let output_runs_no_reg_writes_to id f =
    let non_written_regs = IdSet.diff (write_checked_regs isa) f.trans_regs_written in
    let non_written_regs_no_exc = IdSet.diff (write_checked_regs isa) f.trans_regs_written_no_exc in
    not (IdSet.is_empty non_written_regs_no_exc || IdSet.equal non_written_regs non_written_regs_no_exc) && IdSet.mem id needed_fps
  in
  filter_funs isa output_runs_no_reg_writes_to
    |> List.map (no_reg_writes_to_lemma true isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "";

  filter_funs isa (fun id f -> returns_cap isa f && effectful f)
    |> List.map (return_caps_derivable_lemma isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "";
  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let output_cap_props chan (isa : isa) =
  output_line chan  "theory CHERI_Cap_Properties";
  output_line chan  "imports CHERI_Lemmas";
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
    |> List.map (traces_enabled_lemma false isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let output_mem_props chan (isa : isa) =
  output_line chan  "theory CHERI_Mem_Properties";
  output_line chan  "imports CHERI_Lemmas";
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
    |> List.map (traces_enabled_lemma true isa)
    |> List.map format_lemma |> List.iter (output_line chan);

  output_line chan  "end";
  output_line chan  "";
  output_line chan  "end"

let process_isa file =
  let isa = load_isa file !opt_src_dir in
  let out_file name = Filename.concat !opt_out_dir name in

  let chan = open_out (out_file "CHERI_Gen_Lemmas.thy") in
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
