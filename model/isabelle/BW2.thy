theory BW2

imports "Carry_Val"

begin

text \<open>
Upgrade of the existing Word_Bitwise conversion to booleans.

The main change is, the whole mechanism now permits sharing of
repeated terms using let bindings. Values of word type may be
let bound in input problems. The core tactic produces let
bindings of shared boolean values. A final step can discard
them (compatibility with previous version) or lift them to
fresh meta-bound variables. The latter form seems to be quite
compatible with the Argo solver.
\<close>

lemma minus_one_nat_case:
  "(n - 1) = (case n of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> j)"
  by (simp split: nat.split)

lemma upt_Suc_left:
  "upt (Suc i) j = (if j = 0 then [] else map Suc (upt i (j - 1)))"
  by (cases j, simp_all add: map_Suc_upt)

lemma upt_map_diff:
  "upt i j = map ((+) i) (upt 0 (j - i))"
  using map_add_upt[of i "j - i", symmetric]
  by (cases "i \<le> j", simp_all)

lemma word_if_add_let:
  "(if P then (x :: ('a :: len0) word) else y) = (let switch = P in id If switch x y)"
  by simp

ML \<open>
structure Let_Alt = struct

fun is_atom (_ $ _) = false
  | is_atom (Abs _) = false
  | is_atom _ = true

val def = @{thm Let_def}

fun count_bv i (Bound j) = if i = j then 1 else 0
  | count_bv i (f $ x) = count_bv i f + count_bv i x
  | count_bv i (Abs (_, _, t)) = count_bv (i + 1) t
  | count_bv _ _ = 0

fun simproc count ct = case strip_comb (Thm.term_of ct) of
    (_, [v, Abs (_, _, t)]) => if is_atom v then SOME def
    else if count andalso count_bv 0 t <= 1 then SOME def
    else NONE
  | (_, [_, _]) => SOME def
  | _ => NONE

fun has_bv (Bound _) = true
  | has_bv (Abs _) = true
  | has_bv (f $ x) = has_bv f orelse has_bv x
  | has_bv _ = false

fun count_no_bv pred (t :: ts) tab = let
    val ts = case t of
        f $ x => f :: x :: ts
      | Abs (_, _, t) => t :: ts
      | _ => ts
    val tab = if has_bv t then tab
        else if pred t then Termtab.map_default (t, 0) (fn i => i + 1) tab
        else tab
  in count_no_bv pred ts tab end
  | count_no_bv _ [] tab = tab

val sym_def = @{thm Let_def[symmetric]}

fun add_let_conv ctxt nm x ct = let
    val abs = Thm.lambda_name (nm, x) ct
  in Drule.infer_instantiate ctxt [(("f", 0), abs), (("s", 0), x)] sym_def end

fun let_gather_dup_conv_1 ctxt f ct = let
    val count = count_no_bv f [Thm.term_of ct] Termtab.empty
    val xs = Termtab.dest count
      |> filter (fn (_, j) => j >= 2)
      |> map fst
      |> filter (not o is_atom)
    fun get_greatest [] t _ = t
      | get_greatest (x :: xs) t sz = if size_of_term x > sz
        then get_greatest xs x (size_of_term x)
        else get_greatest xs t sz
    fun get_greatest2 xs = get_greatest (tl xs) (hd xs) (size_of_term (hd xs))
  in if null xs then Conv.no_conv ct
    else add_let_conv ctxt "x" (Thm.cterm_of ctxt (get_greatest2 xs)) ct
  end

fun let_gather_dup_conv ctxt f = Conv.repeat_conv (let_gather_dup_conv_1 ctxt f)

fun let_gather_dup_tac ctxt f = CONVERSION
    (Conv.params_conv ~1 (fn ctxt => Conv.concl_conv ~1 (Conv.arg_conv
        (let_gather_dup_conv ctxt f))) ctxt)

fun abs_name (Abs (nm, _, _)) = nm
  | abs_name _ = "x"

fun find_let ((t as (Const (@{const_name Let}, _) $ v $ f)) :: _) = SOME (abs_name f, v, t)
  | find_let (f $ x :: xs) = find_let (f :: x :: xs)
  | find_let (_ :: xs) = find_let xs
  | find_let [] = NONE

fun let_atom_conv1 ct = case Thm.term_of ct of
  (Const (@{const_name Let}, _) $ x $ _) =>
    if is_atom x then Conv.rewr_conv @{thm Let_def} ct
    else Conv.no_conv ct
  | _ => Conv.no_conv ct

fun let_atom_conv ctxt = Conv.top_conv (K (Conv.try_conv let_atom_conv1)) ctxt

fun let_to_top_conv ctxt ct = case Thm.term_of ct of
    Const (@{const_name Let}, _) $ _ $ Abs _ =>
    Conv.arg_conv (Conv.abs_conv (let_to_top_conv o snd) ctxt) ct
  | t => (case find_let [t] of
    NONE => Conv.all_conv ct
  | SOME (nm, v, _) => Conv.every_conv [add_let_conv ctxt nm (Thm.cterm_of ctxt v),
    let_atom_conv ctxt, let_to_top_conv ctxt] ct
  )

fun let_to_top_tac ctxt = CONVERSION
    (Conv.params_conv ~1 (fn ctxt => Conv.concl_conv ~1 (Conv.arg_conv
        (let_to_top_conv ctxt))) ctxt)

end
\<close>

simproc_setup let_alt ("Let v f") = \<open>K (K (Let_Alt.simproc true))\<close>
declare [[simproc del: let_alt]]
simproc_setup let_atom ("Let v f") = \<open>K (K (Let_Alt.simproc false))\<close>
declare [[simproc del: let_atom]]

lemma let_eq_impI:
  "(\<And>x. v = x \<Longrightarrow> P x) \<Longrightarrow> let x = v in P x"
  by simp

lemmas carry_let_eq_impI = let_eq_impI[where v="carry_val x y c", unfolded carry_val_word_eq_eq]
  for x :: "('a :: len) word" and y c

lemmas word_let_eq_impI = let_eq_impI[where v=x, unfolded word_bit_eq_iff]
  for x :: "('a :: len) word"

lemma case_nat_eq_If:
  "(case n of 0 \<Rightarrow> x | Suc i \<Rightarrow> f i) = (if n = 0 then x else f (n - 1))"
  by (cases n, auto)

lemma ball_insert:
  "(\<forall>x \<in> insert y S. P x) = (P y \<and> (\<forall>x \<in> S. P x))"
  by simp

lemmas imp_to_id = id_apply[where x="(\<longrightarrow>)", THEN fun_cong, THEN fun_cong, symmetric]

ML \<open>
structure Mk_Cache_Simproc = struct

fun app cache ss ctxt ct = case Termtab.lookup (! cache) (Thm.term_of ct) of
    SOME v => v
  | NONE => let
    val res = Simplifier.rewrite (put_simpset ss ctxt) ct
    val res2 = if Thm.is_reflexive res then NONE else SOME res
    val tab = Termtab.insert (K false) (Thm.term_of ct, res2) (! cache)
  in cache := tab; res2 end

fun mk ctxt nm ss lhss = Simplifier.make_simproc ctxt nm
    {lhss = lhss, proc = K (app (Unsynchronized.ref Termtab.empty) ss)}

end
\<close>

ML \<open>
structure BW_Alt = struct

(* strategy:
  1) rewrite with word_via_carry_val and word_if_add_let introducing lets
  (init_tac)
  2a) lift lets to top of goal and then to assumptions (let_eq_impI)
    - also convert carry equals and other word equals to bitwise eqs
  2b) pull assumptions with "bit" or "test_bit" back into the goal
  (let_tac)
  3a) hide implications from the simplifier (imp_to_id)
      and unfold remaining word eqs to bitwise
  3b) simplify with:
    - caching simproc for natural arithmetic and word lengths
    - upt/ball rules
    - bit substitutions
    - exp_eq_zero_iff from Word (2 ^ n = 0 \<longrightarrow> ineq)
  3c) restore implications
  (main_tac)
*)

val no_split_ss =
  simpset_of (put_simpset HOL_ss \<^context>
        delsimprocs [@{simproc let_simp}]
        delsimps @{thms subst_all}
    |> Splitter.del_split @{thm if_split});

val init_ss = simpset_of (put_simpset HOL_basic_ss \<^context> addsimps
   @{thms word_via_carry_val word_if_add_let})

fun init_tac ctxt =
    simp_tac (put_simpset init_ss ctxt addsimprocs [@{simproc let_alt}])

val is_word = can Word_Lib.dest_wordT o fastype_of

fun rev_mp_prems_step_tac pred ctxt = DETERM o SUBGOAL (fn (t, i) => let
    val prems = Logic.strip_assums_hyp t
    val idx = find_index (fn t => can HOLogic.dest_Trueprop t andalso pred t) prems
  in
    if idx = ~1 then no_tac
    else EVERY' [rotate_tac idx, eresolve_tac ctxt @{thms rev_mp}, rotate_tac (~ idx)] i
  end)

fun rev_mp_prems_tac pred ctxt = REPEAT_DETERM o (rev_mp_prems_step_tac pred ctxt)

fun let_to_imp_step ctxt = FIRST'
  [resolve_tac ctxt @{thms carry_let_eq_impI word_let_eq_impI let_eq_impI},
   CHANGED o Let_Alt.let_to_top_tac ctxt,
   CHANGED o Let_Alt.let_gather_dup_tac ctxt is_word]

fun let_to_imp_tac ctxt = TRY o REPEAT_ALL_NEW (let_to_imp_step ctxt)

fun let_tac ctxt = let_to_imp_tac ctxt
    THEN_ALL_NEW rev_mp_prems_tac (exists_Const (fn (s, _) => s = @{const_name bit})) ctxt

val len_ss = put_simpset (simpset_of \<^theory_context>\<open>Type_Length\<close>) @{context}
        delsimps @{thms bit_0}
    |> simpset_of;

fun mk_arith_simproc ctxt = Mk_Cache_Simproc.mk ctxt "bitwise_arith_cache" len_ss
  (map Logic.varify_global
    [@{term "x + y"}, @{term "x - y"}, @{term "Suc i"}, @{term "x < y"},
        @{term "x = y"}, @{term "x <= y"},
        @{term "len_of x"}])

fun get_bit_simps ctxt = Named_Theorems.get ctxt @{named_theorems bit_simps}

fun main_ss ctxt = put_simpset no_split_ss ctxt
    addsimps @{thms Word.exp_eq_zero_iff
        upt_conv_Cons numeral_2_eq_2[symmetric]
        upt_conv_Nil[OF order_refl]
        list.set ball_insert ball_empty}
    addsimps (get_bit_simps ctxt)
    addsimprocs [mk_arith_simproc ctxt]

fun main_tac ctxt =
    simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms imp_to_id word_bit_eq_iff})
    THEN_ALL_NEW simp_tac (main_ss ctxt)
    THEN_ALL_NEW simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms id_apply simp_thms})

fun tac ctxt = init_tac ctxt
    THEN_ALL_NEW let_tac ctxt
    THEN_ALL_NEW main_tac ctxt

(* also pull in assumptions that can be rewritten bitwise *)

fun asm ctxt = full_simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps @{thms word_ineq_via_carry_val word_bit_eq_iff})
    THEN_ALL_NEW rev_mp_prems_tac (exists_Const (fn (s, _) => s = @{const_name bit}
        orelse s = @{const_name carry_val})) ctxt

fun asm_tac ctxt = asm ctxt THEN_ALL_NEW tac ctxt

end
\<close>

method_setup let_dup_word =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (Let_Alt.let_gather_dup_tac ctxt BW_Alt.is_word 1))\<close>
  "gather repeated word terms using let-binding"

method_setup word_bitwise_eq =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (BW_Alt.tac ctxt 1))\<close>
  "decomposer for word equalities and inequalities into bit propositions,
    lifting shared booleans to variables"

lemma (* testing *)
  fixes x :: "8 word" and y :: "6 word"
  shows "or (and (ucast x) (xor y 0)) (xor y 0) = y"
  apply (tactic \<open>BW_Alt.init_tac @{context} 1\<close>)
  apply (tactic \<open>BW_Alt.let_tac @{context} 1\<close>)
  apply (tactic \<open>BW_Alt.main_tac @{context} 1\<close>)
  apply blast
  done

lemma (* testing *)
  fixes x :: "8 word" and y :: "6 word"
  shows "or (and (ucast x) (xor y 0)) (xor y 0) = y"
  apply word_bitwise_eq
  apply blast
  done

end


lemma test_bit_is_slice_check:
  fixes x :: "('a :: len) word"
  shows "bit x n = (Word.slice n x = (1 :: 1 word))"
  unfolding word_bit_eq_iff
  using bit_imp_le_length[of x n]
  by (auto simp add: bit_simps simp flip: bit_0)

lemma word_set_bit_to_smt:
  fixes x :: "('a :: len0) word"
  shows
  "set_bit x n b = (x AND NOT (Bits.shiftl 1 n)) OR (Bits.shiftl (if b then 1 else 0) n)"
  by (auto simp: word_eq_iff test_bit_set_gen word_ops_nth_size nth_shiftl word_size)

lemma slice_up_is_ucast[OF refl, unfolded word_size]:
  "y = ucast (Bits.shiftr x n) \<Longrightarrow> size x < size y + n \<Longrightarrow> Word.slice n x = y"
  by (simp add: slice_shiftr)

lemma cast_down_is_slice[OF refl, unfolded word_size]:
  "y = Word.slice 0 x \<Longrightarrow>
    size y < size x \<Longrightarrow>
    ucast x = y \<and> scast x = y"
  by (simp add: ucast_slice down_cast_same[symmetric] word_size
    is_down_def source_size_def target_size_def)

named_theorems to_smt_word

lemmas to_smt_word_init[to_smt_word] = test_bit_is_slice_check 
    word_set_bit_to_smt
    max_word_def mask_def
    slice_up_is_ucast[unfolded word_size] cast_down_is_slice
    One_nat_def[symmetric]

named_theorems to_smt_word_del
lemmas to_smt_word_del_init[to_smt_word_del] = One_nat_def[to_smt_word_del]

ML \<open>
fun smt_word_tac ctxt = BW_Alt.let_to_imp_tac ctxt
    THEN' full_simp_tac (ctxt
    addsimps Named_Theorems.get ctxt @{named_theorems to_smt_word}
    delsimps Named_Theorems.get ctxt @{named_theorems to_smt_word_del}
    |> Splitter.del_split @{thm if_split})
    THEN' SMT_Solver.smt_tac (ctxt
        |> Config.put SMT_Systems.z3_extensions true
        |> Config.put SMT_Config.oracle true
        |> Config.put SMT_Config.statistics true
) []
\<close>

method_setup smt_word =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (smt_word_tac ctxt 1))\<close>
  "wrapper for oracle-based word/bitvector SMT proofs"

end
