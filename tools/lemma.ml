open Arch
open Analyse_sail
open Ast_util

type lemma =
  { name : string;
    attrs : string;
    assms : string list;
    stmts : string list;
    using : string list;
    unfolding : string list;
    proof : string }

let mk_lemma ~name ~attrs ~stmts ~assms ~proof ~using ~unfolding =
  let using = Util.option_default (if assms = [] then [] else ["assms"]) using in
  { name; attrs; assms; stmts; using; unfolding; proof }

let mangle_name renames n =
  (try Bindings.find n renames with Not_found -> isa_name n)

let mangle_fun_name arch = mangle_name arch.fun_renames
let mangle_reg_ref arch n = mangle_name arch.reg_ref_renames (append_id n "_ref")

let format_fun_name arch id = mangle_fun_name arch id
let format_fun_args f = String.concat " " (List.mapi (fun i _ -> "arg" ^ string_of_int i) f.arg_typs)
let format_fun_call arch id f = format_fun_name arch id ^ " " ^ format_fun_args f

let dquot s = "\"" ^ s ^ "\""

let format_lemma l =
  let shows = if l.assms = [] then "  " else "  shows " in
  let stmt_sep = if l.assms = [] then "\n  " else "\n    and " in
  "lemma " ^ l.name ^ l.attrs ^ ":\n" ^
  (if l.assms = [] then "" else "  assumes " ^ String.concat " and " (List.map dquot l.assms) ^ "\n") ^
  shows ^ String.concat stmt_sep (List.map dquot l.stmts) ^ "\n" ^
  (if l.using = [] then "" else "  using " ^ String.concat " " l.using ^ "\n") ^
  (if l.unfolding = [] then "" else "  unfolding " ^ String.concat " " l.unfolding ^ "\n") ^
  "  by " ^ l.proof ^ "\n"
