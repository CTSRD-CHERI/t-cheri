open Yojson.Basic.Util
open Arch
open Lemma

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let isa_name = "CHERI_RISCV"
let thy_name = isa_name ^ "_Gen_Lemmas"
let thy_imports = isa_name ^ "_Instantiation"

let cap_regs = StringSet.of_list [
  "MEPCC";
  "MScratchC";
  "MTDC";
  "MTCC";
  "SEPCC";
  "SScratchC";
  "STDC";
  "STCC";
  "UEPCC";
  "UScratchC";
  "UTDC";
  "UTCC";
  "DDC";
  "nextPCC";
  "PCC";
  "x31";
  "x30";
  "x29";
  "x28";
  "x27";
  "x26";
  "x25";
  "x24";
  "x23";
  "x22";
  "x21";
  "x20";
  "x19";
  "x18";
  "x17";
  "x16";
  "x15";
  "x14";
  "x13";
  "x12";
  "x11";
  "x10";
  "x9";
  "x8";
  "x7";
  "x6";
  "x5";
  "x4";
  "x3";
  "x2";
  "x1";
  "Xs";
  ]
let extra_cap_funs = StringSet.of_list []
let privileged_regs = StringSet.of_list [
  "UTCC"; "UTDC"; "UScratchC"; "UEPCC"; "STCC"; "STDC"; "SScratchC"; "SEPCC"; "MTCC"; "MTDC"; "MScratchC"; "MEPCC"; "uccsr"; "sccsr"; "mccsr"]
let cap_inv_regs = StringSet.of_list ["PCC"]
let mem_inv_regs = StringSet.of_list []
let conf_regs = StringSet.of_list []
let fun_renames = []
let reg_ref_renames = []
let cap_types = StringSet.of_list ["Capability"]
let skip_funs = StringSet.of_list []

let extra_cap_reg_assms = []

type fun_info =
  { name : string;
    arg_typs : string list;
    ret_typ : string;
    effects : StringSet.t;
    calls : StringSet.t;
    regs_read : StringSet.t;
    regs_written : StringSet.t;
    trans_regs_read : StringSet.t;
    trans_regs_written : StringSet.t }

let fun_info_of_json j =
  { name = member "name" j |> to_string;
    arg_typs = member "arg_typs" j |> convert_each to_string;
    ret_typ = member "ret_typ" j |> to_string;
    effects = member "effects" j |> convert_each to_string |> StringSet.of_list;
    calls = member "calls" j |> convert_each to_string |> StringSet.of_list;
    regs_read = member "regs_read" j |> convert_each to_string |> StringSet.of_list;
    regs_written = member "regs_written" j |> convert_each to_string |> StringSet.of_list;
    trans_regs_read = member "trans_regs_read" j |> convert_each to_string |> StringSet.of_list;
    trans_regs_written = member "trans_regs_written" j |> convert_each to_string |> StringSet.of_list;
  }

let sets_overlap a b = not (StringSet.is_empty (StringSet.inter a b))

let effectful f = not (StringSet.is_empty f.effects)
let has_mem_eff f =
  let mem_effs = StringSet.of_list ["rmem"; "rmemt"; "wmem"; "wmemt"; "wmv"; "wmvt"; "eamem"] in
  sets_overlap f.effects mem_effs

let reads rs f = sets_overlap rs f.trans_regs_read
let writes rs f = sets_overlap rs f.trans_regs_written
let uses rs f = (reads rs f || writes rs f)
let returns_cap f = StringSet.mem f.ret_typ cap_types
let is_cap_fun f = has_mem_eff f || uses cap_regs f || (StringSet.mem f.name extra_cap_funs) || (sets_overlap f.calls extra_cap_funs)

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

let mangle_name renames n =
  (try List.assoc n renames with Not_found -> n)
  |> String.map (fun c -> if c = '#' then '_' else c)
  |> lstrip (fun c -> c = '_')
  |> rstrip (fun c -> c = '_')
let mangle_fun_name = mangle_name fun_renames
let mangle_reg_ref n = mangle_name reg_ref_renames (n ^ "_ref")

let format_fun_name f = mangle_fun_name (f.name)
let format_fun_args f = String.concat " " (List.mapi (fun i _ -> "arg" ^ string_of_int i) f.arg_typs)
let format_fun_call f = format_fun_name f ^ " " ^ format_fun_args f

type lemma =
  { name : string;
    attrs : string;
    assms : string list;
    stmts : string list;
    using : string;
    unfolding : string;
    proof : string }

let mk_lemma name assms stmts = { name = name; attrs = ""; assms = assms; stmts = stmts; using = (if assms = [] then "" else "assms"); unfolding = ""; proof = "auto" }

let dquot s = "\"" ^ s ^ "\""

let format_lemma l =
  let shows = if l.assms = [] then "  " else "  shows " in
  let stmt_sep = if l.assms = [] then "\n  " else "\n    and " in
  "lemma " ^ l.name ^ l.attrs ^ ":\n" ^
  (if l.assms = [] then "" else "  assumes " ^ String.concat " and " (List.map dquot l.assms) ^ "\n") ^
  shows ^ String.concat stmt_sep (List.map dquot l.stmts) ^ "\n" ^
  (if l.using = "" then "" else "  using " ^ l.using ^ "\n") ^
  (if l.unfolding = "" then "" else "  unfolding " ^ l.unfolding ^ "\n") ^
  "  by " ^ l.proof ^ "\n"

let cap_ref_typs = StringSet.map (fun t -> "register(" ^ t ^ ")") cap_types
let is_ref_typ t = Str.string_match (Str.regexp "register(.*)") t 0
let has_ref_args f = List.exists is_ref_typ f.arg_typs

let format_non_cap_exp_lemma f =
  (*let template =
    "lemma non_cap_exp_%s[non_cap_expI]:\n" ^
    "  \"non_cap_exp (%s)\"\n" ^
    "  by (non_cap_expI simp: %s_def)\n"
  in*)
  let get_arg_assm i r = if (is_ref_typ r && not (StringSet.mem r cap_ref_typs)) then ["non_cap_reg arg" ^ string_of_int i] else [] in
  let assms = List.concat (List.mapi get_arg_assm f.arg_typs) in
  format_lemma { (mk_lemma ("non_cap_exp_" ^ format_fun_name f) assms ["non_cap_exp (" ^ format_fun_call f ^ ")"]) with proof = ("(non_cap_expI simp: " ^ format_fun_name f ^ "_def)"); attrs = "[non_cap_expI]" }
  (* let fmt = Scanf.format_from_string template "%s %s %s" in
  let name = format_fun_name f in
  Printf.sprintf fmt name (format_fun_call f) name *)

let format_non_mem_exp_lemma f =
  format_lemma { (mk_lemma ("non_mem_exp_" ^ format_fun_name f) [] ["non_mem_exp (" ^ format_fun_call f ^ ")"]) with proof = ("(non_mem_expI simp: " ^ format_fun_name f ^ "_def)"); attrs = "[non_mem_expI]" }

let format_no_reg_writes_to_lemma f =
  let name = format_fun_name f in
  let regs = StringSet.elements f.trans_regs_written in
  let reg_names = List.map (fun r -> "''" ^ r ^ "''") regs in
  let reg_refs = List.map mangle_reg_ref regs in
  let reg_defs = List.map (fun n -> n ^ "_def") (reg_refs) in
  let get_arg_assm i r = if (is_ref_typ r && not (StringSet.mem r cap_ref_typs)) then ["name arg" ^ string_of_int i ^ " \\<notin> Rs"] else [] in
  let assms = (if regs = [] then [] else ["{" ^ String.concat ", " reg_names ^ "} \\<inter> Rs = {}"]) @ List.concat (List.mapi get_arg_assm f.arg_typs) in
  (*let assm =
    if regs = [] then "" else
      "  assumes \"{" ^ String.concat ", " reg_names ^ "} \\<inter> Rs = {}\"\n"
  in
  let using = if regs = [] then "" else "using assms " in*)
  let simps = if regs = [] then "" else " simp: " ^ String.concat " " reg_defs in
  format_lemma { (mk_lemma ("no_reg_writes_to_" ^ name) assms ["no_reg_writes_to Rs (" ^ format_fun_call f ^ ")"]) with attrs = "[no_reg_writes_toI, simp]"; unfolding = (name ^ "_def bind_assoc"); proof = ("(no_reg_writes_toI" ^ simps ^ ")") }
  (*"lemma no_reg_writes_to_" ^ name ^ "[no_reg_writes_toI, simp]:\n" ^
  assm ^
  "  shows \"no_reg_writes_to Rs (" ^ format_fun_call f ^ ")\"\n" ^
  "  " ^ using ^ "unfolding " ^ name ^ "_def bind_assoc\n" ^
  "  by (no_reg_writes_toI" ^ simps ^ ")\n"*)

let format_trace_enabled_lemma f =
  "lemma trace_enabled_" ^ format_fun_name f ^ "[trace_elim]:\n" ^
  "  assumes \"(" ^ format_fun_call f ^ ", t, m') \\<in> Traces\"\n" ^
  "  shows \"trace_enabled s t\"\n" ^
  "  using assms\n" ^
  "  by (trace_enabledI simp: " ^ format_fun_name f ^ "_def)\n"

let format_return_caps_derivable_lemma (f : fun_info) =
  format_lemma { (mk_lemma (f.name ^ "_derivable") ["Run_inv (" ^ format_fun_call f ^ ") t c regs"] ["c \\<in> derivable_caps (run s t)"]) with attrs = "[derivable_capsE]"; unfolding = (format_fun_name f ^ "_def"); proof = "- (derivable_capsI assms: assms)" }

let format_traces_enabled_lemma f =
  let cap_regs_read = StringSet.inter cap_regs (StringSet.union f.regs_read (StringSet.diff f.trans_regs_read privileged_regs)) in
  let cap_reg_names = List.map (fun r -> "''" ^ r ^ "''") (StringSet.elements cap_regs_read) in
  let cap_assm =
    if sets_overlap cap_regs_read privileged_regs || (writes cap_regs f && not (StringSet.is_empty cap_regs_read)) then
      ["{" ^ String.concat ", " cap_reg_names ^ "} \\<subseteq> accessible_regs s"]
    else []
  in
  let arg_assms =
    if has_mem_eff f || writes cap_regs f || StringSet.mem f.name extra_cap_funs then
      List.concat (List.mapi (fun i t -> if StringSet.mem t cap_types then ["arg" ^ string_of_int i ^ " \\<in> derivable_caps s"] else []) f.arg_typs)
    else []
  in
  let add_extra_assm (f', assm) assms = if StringSet.mem f' f.calls then StringSet.add assm assms else assms in
  let extra_assms = List.fold_right add_extra_assm extra_cap_reg_assms StringSet.empty in
  let assms = List.map dquot (cap_assm @ arg_assms @ StringSet.elements extra_assms) in
  let assumes = if assms = [] then "" else "  assumes " ^ String.concat " and " assms  ^ "\n" in
  let using = if assms = [] then "" else " assms: assms" in
  (if returns_cap f then
     format_lemma { (mk_lemma (f.name ^ "_derivable") (("Run_inv (" ^ format_fun_call f ^ ") t c regs") :: assms) ["c \\<in> derivable_caps (run s t)"]) with attrs = "[derivable_capsE]"; unfolding = (format_fun_name f ^ "_def"); proof = "- (derivable_capsI assms: assms)" } ^ "\n"
   else "") ^
  "lemma traces_enabled_" ^ format_fun_name f ^ "[traces_enabledI]:\n" ^
  assumes ^
  "  shows \"traces_enabled (" ^ format_fun_call f ^ ") s regs\"\n" ^
  "  unfolding " ^ format_fun_name f ^ "_def bind_assoc\n" ^
  "  by (traces_enabledI" ^ using ^ ")\n"

let json = Yojson.Basic.from_file "fp.json"
let fun_infos =
  Yojson.Basic.from_file "fp.json"
  |> member "fun_infos"
  |> to_list
  |> List.map fun_info_of_json
  |> List.filter (fun f -> effectful f && not (StringSet.mem f.name skip_funs))

let non_cap_funs = List.filter (fun f -> not (is_cap_fun f)) fun_infos
let non_mem_funs = List.filter (fun f -> not (has_mem_eff f)) fun_infos
let cap_funs = List.filter (fun f -> is_cap_fun f) fun_infos
let mem_funs = List.filter (fun f -> has_mem_eff f) fun_infos

let find_strings x m = try StringMap.find x m with Not_found -> StringSet.empty

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
  StringSet.diff (List.fold_left add_used_regs StringSet.empty fun_infos) conf_regs

let non_cap_regs_lemma =
  let non_cap_regs = StringSet.elements (StringSet.diff regs_used (StringSet.union cap_regs privileged_regs)) in
  let stmts = List.map (fun r -> "  \"non_cap_reg " ^ mangle_reg_ref r ^ "\"") non_cap_regs in
  let defs = List.mapi (fun i r -> mangle_reg_ref r ^ "_def" ^ (if i mod 5 = 4 then "\n    " else "")) non_cap_regs in
  "lemma non_cap_regsI[intro, simp]:\n" ^
  String.concat "\n" stmts ^ "\n" ^
  "  unfolding " ^ String.concat " " defs ^ "\n" ^
  "  by (auto simp: non_cap_reg_def)\n"

let write_cap_regs_lemma =
  let stmts = List.map (fun r -> "\"traces_enabled (write_reg " ^ mangle_reg_ref r ^ " c) s regs\"") (StringSet.elements cap_regs) in
  let defs = List.mapi (fun i r -> mangle_reg_ref r ^ "_def" ^ (if i mod 5 = 4 then "\n                " else "")) (StringSet.elements cap_regs) in
  "lemma traces_enabled_write_cap_regs[traces_enabledI]:\n" ^
  "  assumes \"c \\<in> derivable_caps s\"\n" ^
  "  shows " ^ String.concat "\n    and " stmts ^ "\n" ^
  "  using assms\n" ^
  "  by (intro traces_enabled_write_reg;\n" ^
  "      auto simp: " ^ String.concat " " defs ^ " derivable_caps_def)+\n"

let read_cap_regs_lemma =
  let stmt r =
    let assms = if StringSet.mem r privileged_regs then "system_reg_access s \\<or> has_ex \\<Longrightarrow> " else "" in
    "  \"" ^ assms ^ "traces_enabled (read_reg " ^ mangle_reg_ref r ^ ") s regs\""
  in
  let stmts = List.map stmt (StringSet.elements cap_regs) in
  let defs = List.mapi (fun i r -> mangle_reg_ref r ^ "_def" ^ (if i mod 5 = 4 then "\n                " else "")) (StringSet.elements cap_regs) in
  "lemma traces_enabled_read_cap_regs[traces_enabledI]:\n" ^
  String.concat "\n" stmts ^ "\n" ^
  "  by (intro traces_enabled_read_reg;\n" ^
  "      auto simp: " ^ String.concat " " defs ^ ")+\n"

let non_inv_regs_lemma inv_regs =
  let non_inv_regs = StringSet.elements (StringSet.diff regs_used inv_regs) in
  let stmts = List.map (fun r -> "  \"\\<And>v. traces_preserve_invariant (write_reg " ^ mangle_reg_ref r ^ " v)\"") non_inv_regs in
  let defs = List.mapi (fun i r -> mangle_reg_ref r ^ "_def" ^ (if i mod 5 = 4 then "\n    " else "")) non_inv_regs in
  "lemma preserves_invariant_write_non_inv_regs[preserves_invariantI]:\n" ^
  String.concat "\n" stmts ^ "\n" ^
  "  unfolding " ^ String.concat " " defs ^ "\n" ^
  "  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+\n"

let preserves_invariant_stmt runs f =
  let get_arg_assm i r = if (is_ref_typ r && not (StringSet.mem r cap_ref_typs)) then ["name arg" ^ string_of_int i ^ " \\<notin> inv_regs"] else [] in
  let assms = (List.concat (List.mapi get_arg_assm f.arg_typs)) in
  let stmt = (if runs then "runs" else "traces") ^ "_preserve_invariant (" ^ format_fun_call f ^ ")" in
  (assms, stmt)

let format_preserves_invariant_lemma f =
  let (assms, stmt) = preserves_invariant_stmt true f in
  format_lemma
    { (mk_lemma ("preserves_invariant_" ^ format_fun_name f) assms [stmt])
      with proof = "preserves_invariantI"; attrs = "[preserves_invariantI]";
           unfolding = (format_fun_name f ^ "_def bind_assoc") }

let preserve_inv_no_writes_lemma fs =
  let stmt f =
    let (assms, stmt) = preserves_invariant_stmt false f in
    "\\<And>" ^ format_fun_args f ^ ". " ^ (if assms = [] then "" else String.concat " \\<Longrightarrow> " (assms @ [""])) ^ stmt
  in
  { (mk_lemma "preserves_invariant_no_writes_to_inv_regs" [] (List.map stmt fs))
    with proof = "(intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp)+";
         attrs = "[preserves_invariantI]" }

let read_cap_regs_derivable_lemma =
  let stmt r = "\\<And>t c regs s. Run_inv (read_reg " ^ mangle_reg_ref r ^ ") t c regs \\<Longrightarrow> {''" ^ r ^ "''} \\<subseteq> accessible_regs s \\<Longrightarrow> c \\<in> derivable_caps (run s t)" in
  let defs = List.mapi (fun i r -> mangle_reg_ref r ^ "_def" ^ (if i mod 5 = 4 then "\n    " else "")) (StringSet.elements cap_regs) in
  let unfolding = String.concat " " defs ^ " Run_inv_def derivable_caps_def" in
  format_lemma { (mk_lemma "read_cap_regs_derivable" [] (List.map stmt (StringSet.elements cap_regs))) with attrs = "[derivable_capsE]"; unfolding = unfolding; proof = "(auto elim!: Run_read_regE intro!: derivable.Copy)" }
;;

print_endline ("theory " ^ thy_name);;
print_endline ("imports " ^ thy_imports);;
print_endline  "begin";;
print_endline  "";;
print_endline ("context " ^ isa_name ^ "_Axiom_Inv_Automaton");;
print_endline  "begin";;
print_endline  "";;

print_endline non_cap_regs_lemma;;
print_endline  "lemmas non_cap_exp_rw_non_cap_reg[non_cap_expI] =";;
print_endline  "  non_cap_regsI[THEN non_cap_exp_read_non_cap_reg]";;
print_endline  "  non_cap_regsI[THEN non_cap_exp_write_non_cap_reg]";;
print_endline  "";;

List.map format_non_cap_exp_lemma non_cap_funs |> List.iter print_endline;;

List.filter (fun f -> (is_cap_fun f || has_ref_args f) && not (has_mem_eff f)) fun_infos
  |> List.map format_non_mem_exp_lemma
  |> List.iter print_endline;;

(*print_endline  "end";;
print_endline  "";;
print_endline ("context " ^ isa_name ^ "_State_Invariant");;
print_endline  "begin";;
print_endline  "";;*)

(*List.filter (fun f -> effectful f && not (writes_inv_reg f) && not (StringSet.mem f.name skip_funs) && StringSet.mem f.name (funs_called_by fun_infos)) fun_infos*)
List.filter (fun (f : fun_info) -> StringSet.mem f.name (funs_called_by fun_infos)) fun_infos
  |> List.map format_no_reg_writes_to_lemma
  |> List.iter print_endline;;

print_endline  "";;

if not (StringSet.is_empty cap_regs) then print_endline read_cap_regs_derivable_lemma;;

print_endline  "end";;
print_endline  "";;
print_endline ("context " ^ isa_name ^ "_Write_Cap_Automaton");;
print_endline  "begin";;
print_endline  "";;

if not (StringSet.is_empty cap_inv_regs) then print_endline (non_inv_regs_lemma cap_inv_regs);;
if not (StringSet.is_empty cap_inv_regs) then print_endline (format_lemma (preserve_inv_no_writes_lemma (List.filter (fun f -> not (writes cap_inv_regs f) && StringSet.mem f.name (funs_called_by fun_infos)) fun_infos)));;
print_endline write_cap_regs_lemma;;
print_endline read_cap_regs_lemma;;
if not (StringSet.is_empty cap_inv_regs) then
  (List.filter (fun f -> writes cap_inv_regs f || not (StringSet.mem f.name (funs_called_by fun_infos))) fun_infos
    |> List.map format_preserves_invariant_lemma
    |> List.iter print_endline);;

print_endline  "";;

print_endline  "lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]\n";;
print_endline  "";;

List.filter is_cap_fun fun_infos
  |> List.map format_traces_enabled_lemma
  |> List.iter print_endline;;

print_endline  "end";;
print_endline  "";;

print_endline ("context " ^ isa_name ^ "_Mem_Automaton");;
print_endline  "begin";;
print_endline  "";;

if not (StringSet.is_empty mem_inv_regs) then begin
  print_endline (non_inv_regs_lemma mem_inv_regs);
  print_endline (format_lemma (preserve_inv_no_writes_lemma (List.filter (fun f -> not (writes mem_inv_regs f) && StringSet.mem f.name (funs_called_by fun_infos)) fun_infos)));
  (List.filter (fun f -> writes mem_inv_regs f || not (StringSet.mem f.name (funs_called_by fun_infos))) fun_infos
    |> List.map format_preserves_invariant_lemma
    |> List.iter print_endline)
end;;

print_endline  "lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]\n";;
print_endline  "lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]\n";;
print_endline  "";;

List.filter has_mem_eff fun_infos
  |> List.map format_traces_enabled_lemma
  |> List.iter print_endline;;

print_endline  "end";;
print_endline  "";;
print_endline  "end";;
