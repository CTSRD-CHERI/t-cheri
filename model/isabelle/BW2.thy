theory BW2

imports "Carry_Val"

begin

text \<open>
Rework of the previous Word_Bitwise conversion to booleans.

The mechanism shares repeated terms using let-bindings and
then equalities. Values of word type may be let bound in input
problems and will not be repeated in the output.

The previous strategy of iterating over lists is dropped.
Instead the @{const bit} constant is expanded by using its
named theorem set.

Ripple/carry effects are managed via the @{const carry_val} carry constant.
\<close>

lemmas bit_if[bit_simps] = if_distrib[where f="\<lambda>x. bit x _"]

lemma bit_unat:
  "bit (unat (w :: ('a :: len) word)) i = bit w i"
  by transfer (simp add: bit_simps)

lemma bit_uint:
  "bit (uint (w :: ('a :: len) word)) i = bit w i"
  by transfer (simp add: bit_simps)

lemma bit_word_numeral_eq_nat:
  "bit (numeral n :: ('a :: len) word) i = bit (take_bit (LENGTH('a)) (numeral n :: nat)) i"
  by (simp add: bit_unat[symmetric])

lemma bit_word_numeral_eq_int:
  "bit (numeral n :: ('a :: len) word) i = bit (take_bit (LENGTH('a)) (numeral n :: int)) i"
  by (simp only: bit_uint[symmetric] uint_bintrunc)

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

fun count_subterms pred (t :: ts) tab = let
    val ts = case t of
        f $ x => f :: x :: ts
      | Abs (_, _, t) => t :: ts
      | _ => ts
    val tab = if pred t andalso null (loose_bnos t)
        then Termtab.map_default (t, 0) (fn i => i + 1) tab
        else tab
  in count_subterms pred ts tab end
  | count_subterms _ [] tab = tab

val sym_def = @{thm Let_def[symmetric]}

fun add_let_conv ctxt nm x ct = let
    val abs = Thm.lambda_name (nm, x) ct
  in Drule.infer_instantiate ctxt [(("f", 0), abs), (("s", 0), x)] sym_def end

fun let_gather_dup_conv_1 ctxt f ct = let
    val count = count_subterms f [Thm.term_of ct] Termtab.empty
    val xs = Termtab.dest count
      |> filter (fn (_, j) => j >= 2)
      |> filter (not o is_atom o fst)
      |> map (fn (t, _) => (size_of_term t, t))
      |> sort (Int.compare o apply2 fst)
      |> rev
  in if null xs then Conv.no_conv ct
    else add_let_conv ctxt "x" (Thm.cterm_of ctxt (snd (hd xs))) ct
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

fun let_to_top_step_conv ctxt ct = let
    val (is_let, foc) = case Thm.term_of ct of
          Const (@{const_name Let}, _) $ x $ Abs _ => (true, x)
        | t => (false, t)
  in case find_let [foc] of
    NONE => if is_let
    then Conv.arg_conv (Conv.abs_conv (let_to_top_step_conv o snd) ctxt) ct
    else Conv.no_conv ct
  | SOME (nm, v, _) => if is_atom v
    then let_atom_conv ctxt ct
    else add_let_conv ctxt nm (Thm.cterm_of ctxt v) ct
  end

fun let_to_top_conv ctxt = Conv.repeat_conv (let_to_top_step_conv ctxt)

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
  "(\<And>x. v = x \<longrightarrow> P x) \<Longrightarrow> let x = v in P x"
  by simp

lemmas carry_let_eq_impI = let_eq_impI[where v="carry_val x y c", unfolded carry_val_word_eq_eq]
  for x :: "('a :: len) word" and y c

lemmas word_let_eq_impI = let_eq_impI[where v=x, unfolded word_bit_eq_iff]
  for x :: "('a :: len) word"

lemma ball_set_simps:
  "(\<forall>x \<in> set (y # ys). P x) = (P y \<and> (\<forall>x \<in> set ys. P x))"
  "(\<forall>x \<in> set []. P x) = True"
  by simp_all

lemma imp_to_id:
  "(P \<longrightarrow> Q) = id (\<longrightarrow>) P Q"
  by simp

lemma bit_num_0[bit_simps]:
  "\<not> bit 0 x"
  by simp

lemmas if_simps = if_bool_eq_disj[where Q=False, simplified]
  if_bool_eq_disj[where R=False, simplified]
  if_bool_eq_conj[where Q=True, simplified]
  if_bool_eq_conj[where R=True, simplified]
  if_True if_False

lemma carry_simps:
  "carry True a b = (a \<or> b)"
  "carry a True b = (a \<or> b)"
  "carry a b True = (a \<or> b)"
  "carry False a b = (a \<and> b)"
  "carry a False b = (a \<and> b)"
  "carry a b False = (a \<and> b)"
  by (auto simp add: carry_def)

lemma bit_word_impossible:
  fixes x :: "('a :: len) word"
  shows "LENGTH ('a) \<le> i \<Longrightarrow> \<not> bit x i"
  by (auto dest: bit_imp_le_length)

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
  1) asm_tac (optional): rewrite equalities/inequalities to include bit
    judgements, and pull all assumptions containing the bit constant into
    the goal.
  2) let_tac: rewrite word arithmetic to use the carry val,
    then lift out carry values, values fixed in lets, and switches of if
    terms up to top-level lets then assumptions
  3) main_tac: first hide implications from the simplifier, then
    do the main simplification phase:
    - bit rewrites (bit_simps)
    - caching simproc for natural arithmetic and word lengths
    - upt/ball expansion rules
    - exponent rule from Word (2-to-the-power-of-n = 0 to ineq)
*)

fun rev_mp_prems_step_tac pred ctxt = DETERM o SUBGOAL (fn (t, i) => let
    val prems = Logic.strip_assums_hyp t
    val idx = find_index (fn t => can HOLogic.dest_Trueprop t andalso pred t) prems
  in
    if idx = ~1 then no_tac
    else EVERY' [rotate_tac idx, eresolve_tac ctxt @{thms rev_mp}, rotate_tac (~ idx)] i
  end)

fun rev_mp_prems_tac pred ctxt = REPEAT_DETERM o (rev_mp_prems_step_tac pred ctxt)

fun asm_tac ctxt = full_simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps @{thms word_ineq_via_carry_val word_bit_eq_iff})
    THEN_ALL_NEW rev_mp_prems_tac (exists_Const (fn (s, _) => s = @{const_name bit})) ctxt

val is_word = can Word_Lib.dest_wordT o fastype_of

fun search_term search_f t = let
    fun sub_ts (f $ x) = [f, x]
      | sub_ts (Abs (_, _, t)) = [t]
      | sub_ts _ = []
    fun f [] = NONE
      | f (t :: ts) = case search_f t of
        SOME x => SOME x
      | NONE => f (sub_ts t @ ts)
  in f [t] end

fun note_let_term t = let
    val (f, xs) = Term.strip_comb t
    val f_nm = fst (dest_Const f)
  in if f_nm = @{const_name carry_val} andalso is_word t
    then SOME (t, true)
    else if f_nm = @{const_name If} andalso is_word t andalso length xs = 3
        andalso not (Let_Alt.is_atom (hd xs))
    then SOME (hd xs, true)
    else if f_nm = @{const_name Let} andalso length xs = 2
    then SOME (hd xs, not (Let_Alt.is_atom (hd xs)))
    else NONE
  end handle TERM _ => NONE

fun pull_let_conv ctxt ct = case search_term note_let_term (Thm.term_of ct) of
    NONE => Conv.no_conv ct
  | SOME (t, lift) => if lift
    then Let_Alt.add_let_conv ctxt "x" (Thm.cterm_of ctxt t) ct
    else Let_Alt.let_atom_conv ctxt ct

fun goal_bool_conv conv ctxt = let
    fun bool_conv ctxt ct = case Thm.term_of ct of
        Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv (conv ctxt) ct
      | _ => Conv.no_conv ct
  in Conv.params_conv ~1 (fn ctxt => Conv.concl_conv ~1 (bool_conv ctxt)) ctxt end

fun pull_let_step ctxt = CONVERSION (goal_bool_conv pull_let_conv ctxt)

fun let_step ctxt = DETERM o FIRST'
  [resolve_tac ctxt @{thms carry_let_eq_impI word_let_eq_impI let_eq_impI},
   CHANGED o pull_let_step ctxt,
   CHANGED o Let_Alt.let_gather_dup_tac ctxt is_word]

fun let_tac ctxt = simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps @{thms word_via_carry_val})
    THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (let_step ctxt))

val len_ss = put_simpset (simpset_of \<^theory_context>\<open>Type_Length\<close>) @{context}
    |> simpset_of;

fun mk_arith_simproc ctxt = Mk_Cache_Simproc.mk ctxt "bitwise_arith_cache" len_ss
  (map Logic.varify_global
    [@{term "x + y"}, @{term "x - y"},
        @{term "x < y"}, @{term "x <= y"},
        @{term "x mod y"},
        @{term "Suc i"}, @{term "pred_numeral n"},
        @{term "nat i"}, @{term "int n"},
        @{term "drop_bit i (n :: nat)"}, @{term "take_bit i (n :: nat)"},
        @{term "bit (i :: int) j"}, @{term "(i :: nat) = j"},
        @{term "len_of x"}])

fun get_bit_simps ctxt = let
    val ss = Named_Theorems.get ctxt @{named_theorems bit_simps}
  in ss end

fun main_ss proc ctxt = put_simpset HOL_ss ctxt
    delsimprocs [@{simproc let_simp}]
    delsimps @{thms subst_all}
    addsimps @{thms Word.exp_eq_zero_iff one_neq_zero
        upt_conv_Cons numeral_2_eq_2[symmetric]
        upt_conv_Nil[OF order_refl]
        ball_set_simps
        nat.case case_nat_numeral[unfolded Let_def]
        bit_word_numeral_eq_int
        o_apply}
    addsimps (get_bit_simps ctxt)
    addsimprocs [proc]
    |> Splitter.del_split @{thm if_split}

fun main_tac ctxt = let
    val proc = mk_arith_simproc ctxt
  in
    simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms imp_to_id word_bit_eq_iff})
    THEN_ALL_NEW simp_tac (main_ss proc ctxt)
    THEN_ALL_NEW simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps @{thms simp_thms carry_simps if_simps
            bit_word_impossible}
        addsimprocs [proc])
    THEN_ALL_NEW simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms id_apply})
  end

fun tac asm ctxt = (if asm then asm_tac ctxt else K all_tac)
    THEN_ALL_NEW let_tac ctxt
    THEN_ALL_NEW main_tac ctxt

fun parse_method s ctxt = let
    val asm = if s = "no_asm" then false
      else if s = "asm" then true
      else if s = "" then true
      else error ("parse_asm_tac: expected (asm) or (no_asm) or none: " ^ s)
  in Method.SIMPLE_METHOD (tac asm ctxt 1) end

end
\<close>

method_setup let_dup_word =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (Let_Alt.let_gather_dup_tac ctxt BW_Alt.is_word 1))\<close>
  "gather repeated word terms using let-binding"

method_setup word_bitwise_eq =
  \<open>Scan.lift Parse.parname >> (BW_Alt.parse_method)\<close>
  "decomposer for word equalities and inequalities into bit propositions,
    lifting shared booleans to variables"

lemma (* testing *)
  fixes x :: "8 word" and y :: "6 word"
  shows "or (and (ucast x) (xor y 0)) (xor y 0) = y"
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

lemma (* testing with carry *)
  fixes x :: "12 word"
  shows "or (and x 53) (and y 72) = (and y 72) + (and x 53)"
  apply (tactic \<open>BW_Alt.let_tac @{context} 1\<close>)
  apply (tactic \<open>BW_Alt.main_tac @{context} 1\<close>)
  apply (clarsimp simp add: carry_def)
  done

lemma (* testing with if *)
  fixes x :: "12 word"
  shows "(if i = j then x else 0) = (and x (if j = i then (-1) else 0))"
  apply (tactic \<open>BW_Alt.let_tac @{context} 1\<close>)
  apply (tactic \<open>BW_Alt.main_tac @{context} 1\<close>)
  apply blast
  done

lemma (* testing with let *)
  fixes x :: "12 word"
  shows "\<And>y :: nat. True \<longrightarrow> (let z = or x 1 in (drop_bit 1 z) = (drop_bit 1 x))"
  apply (tactic \<open>BW_Alt.let_tac @{context} 1\<close>)
  apply (tactic \<open>BW_Alt.main_tac @{context} 1\<close>)
  apply simp
  done

lemma (* more ugly testing *)
  fixes val :: "30 word"
  shows "P \<Longrightarrow> bit val 23 = bit (val + incr) 23 \<Longrightarrow>
    \<not> bit incr 23 \<Longrightarrow> Q val \<Longrightarrow>
    (ucast val AND 16777215) + (ucast incr AND 16777215) \<le> (16777215::64 word)"
  apply (word_bitwise_eq)
  apply (intro impI; simp add: carry_def)
  apply argo
  done

end
