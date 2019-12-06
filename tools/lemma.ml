open Arch

type lemma =
  { name : string;
    attrs : string;
    assms : string list;
    stmts : string list;
    using : string;
    unfolding : string;
    proof : string }

let mk_lemma name assms stmts = { name = name; attrs = ""; assms = assms; stmts = stmts; using = (if assms = [] then "" else "assms"); unfolding = ""; proof = "auto" }

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
  (try StringMap.find n renames with Not_found -> n)
  |> String.map (fun c -> if c = '#' then '_' else c)
  |> lstrip (fun c -> c = '_')
  |> rstrip (fun c -> c = '_')
let mangle_fun_name arch = mangle_name arch.fun_renames
let mangle_reg_ref arch n = mangle_name arch.reg_ref_renames (n ^ "_ref")

let format_fun_name arch (f : fun_info) = mangle_fun_name arch (f.name)
let format_fun_args f = String.concat " " (List.mapi (fun i _ -> "arg" ^ string_of_int i) f.arg_typs)
let format_fun_call arch f = format_fun_name arch f ^ " " ^ format_fun_args f

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
