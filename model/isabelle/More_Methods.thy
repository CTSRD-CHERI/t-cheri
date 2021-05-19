(*
  Miscellaneous additional code, attributes and methods used in some
  proof automation.
*)
theory More_Methods

imports
  Main
  "HOL-Eisbach.Eisbach_Tools"

begin

ML \<open>

structure Simp_Rules = struct

(* provides similar features to setting up a named theorems set
   (e.g. named_theorems xs) and simplifying with it (e.g. (simp only: xs)),
   only the simpset is constructed once per proof rather than once per
   occurence of the method in Eisbach expansions. this can be much faster. *)

fun mk ctxtf thms = (thms, Lazy.lazy (fn () => (put_simpset HOL_basic_ss (ctxtf ())) addsimps thms
    |> simpset_of))

val default = ([], Lazy.value HOL_basic_ss)

fun mk_glob thms = if null thms then default
  else mk (fn () => Proof_Context.init_global (Thm.theory_of_thm (hd thms))) thms

structure Data = Generic_Data
(
  type T = (thm list * simpset Lazy.lazy) Symtab.table;
  val empty: T = Symtab.empty;
  val extend = I;
  val merge : T * T -> T = Symtab.join (K (mk_glob o Thm.merge_thms o apply2 fst))
);

fun add_gen nm thms gctxt = Data.map (Symtab.map_default (nm, default) (fn (prev_thms, _) =>
    mk (fn () => Context.proof_of gctxt) (prev_thms @ thms))) gctxt

fun attr nm = Thm.declaration_attribute (add_gen nm o single)

val (attr_parse : attribute context_parser) = Scan.lift Args.name >> attr

fun get_ss nm ctxt = case Symtab.lookup (Data.get (Context.Proof ctxt)) nm of
    NONE => error ("Simp_Rules.get_ss: rule set not found: " ^ nm)
  | SOME (_, ss) => Lazy.force ss

fun set_ss nm ctxt = put_simpset (get_ss nm ctxt) ctxt

fun simp_concl_tac nm ctxt = simp_tac (set_ss nm ctxt)

fun simp_asm_tac nm ctxt = full_simp_tac (set_ss nm ctxt)

fun simp_concl_method nm ctxt = Method.SIMPLE_METHOD (simp_concl_tac nm ctxt 1)

fun simp_asm_method nm ctxt = Method.SIMPLE_METHOD (simp_asm_tac nm ctxt 1)

end
\<close>

attribute_setup simp_rules_add = \<open>Simp_Rules.attr_parse\<close>

method_setup simp_rules_concl = \<open>Scan.lift Args.name >> Simp_Rules.simp_concl_method\<close>
method_setup simp_rules_asm = \<open>Scan.lift Args.name >> Simp_Rules.simp_asm_method\<close>

end

