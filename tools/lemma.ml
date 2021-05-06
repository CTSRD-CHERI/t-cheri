open Ast_util

type lemma =
  { name : string;
    attrs : string;
    assms : string list;
    stmts : string list;
    using : string list;
    unfolding : string list;
    proof : string }

type lemma_override =
  { name_override : string option;
    attrs_override : string option;
    assms_override : string list option;
    extra_assms : string list;
    stmts_override : string list option;
    using_override : string list option;
    unfolding_override : string list option;
    proof_override : string option }

let mk_lemma ~name ~attrs ~stmts ~assms ~proof ~using ~unfolding =
  let using = Util.option_default (if assms = [] then [] else ["assms"]) using in
  { name; attrs; assms; stmts; using; unfolding; proof }

let dquot s = "\"" ^ s ^ "\""

let format_lemma l =
  let shows = if l.assms = [] then "  " else "  shows " in
  let stmt_sep = if l.assms = [] then "\n  " else "\n    and " in
  "lemma " ^ l.name ^ l.attrs ^ ":\n" ^
  (if l.assms = [] then "" else "  assumes " ^ String.concat " and " (List.map dquot l.assms) ^ "\n") ^
  shows ^ String.concat stmt_sep (List.map dquot l.stmts) ^ "\n" ^
  (if l.using = [] then "" else "  using " ^ String.concat " " l.using ^ "\n") ^
  (if l.unfolding = [] then "" else "  unfolding " ^ String.concat " " l.unfolding ^ "\n") ^
  (if l.proof = "sorry" then "  sorry" else ("  by " ^ l.proof)) ^ "\n"

let apply_override o l =
  (* let using = match (o.using_override, l.using, o.assms_override, l.assms) with
    | (Some using, _, _, _) -> using
    | (None, using, Some (_ :: _), []) when not (List.mem "assms" using) -> "assms" :: using
    | (_, using, _, _) -> using
  in *)
  let using = Util.option_default l.using o.using_override in
  { name = Util.option_default l.name o.name_override;
    attrs = Util.option_default l.attrs o.attrs_override;
    assms = (Util.option_default l.assms o.assms_override) @ o.extra_assms;
    stmts = Util.option_default l.stmts o.stmts_override;
    using = using;
    unfolding = Util.option_default l.unfolding o.unfolding_override;
    proof = Util.option_default l.proof o.proof_override;
  }
