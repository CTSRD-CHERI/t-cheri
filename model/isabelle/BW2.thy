theory BW2

imports "HOL-Word.Word_Bitwise"

begin

text \<open>
Facts about the "carry" value. The carry object for x and y
is, at every bit position, the value that would have been
carried in during an addition of x and y. This can be used
to rewrite additions and inequalities to factor out the
components that move between bit positions.
\<close>

definition
  carry_val :: "('a :: {bit_operations, plus, zero, one}) \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
  where
  "carry_val x y c = (x + y + (if c then 1 else 0)) XOR (x XOR y)"

(* easy enough to define, no idea how to prove anything about it *)

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

lemma rbl_word_if_let: "rev (to_bl (if P then x else y)) =
    (let c = P in map2 (If c) (rev (to_bl x)) (rev (to_bl y)))"
  by (simp add: Product_Type.split_def)

fun carry_chain :: "(bool * bool) list \<Rightarrow> bool \<Rightarrow> bool list"
  where
    "carry_chain [] x = []"
  | "carry_chain (x # xs) y = y # carry_chain xs (carry (fst x) (snd x) y)"

lemma length_carry_chain[simp]:
  "length (carry_chain xs c) = length xs"
  by (induct xs arbitrary: c, simp_all)

lemma carry_chain_eq_Nil[simp]:
  "(carry_chain xs c = []) = (xs = [])"
  by (cases xs, simp_all)

definition carry_word :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> bool \<Rightarrow> 'a word"
  where
  "carry_word x y c = of_bl (rev (carry_chain (zip (rev (to_bl x)) (rev (to_bl y))) c))"

lemma rbl_plus_carry_chain:
  "length xs = length ys \<Longrightarrow>
    rbl_plus c xs ys = map (\<lambda>(c, (x, y)). xor3 x y c)
        (zip (carry_chain (zip xs ys) c) (zip xs ys))"
  by (induct arbitrary: c rule: list_induct2, simp_all add: rbl_plus_simps)

lemma carry_word_eq_xor:
  "carry_word x y False = ((x + y) XOR x XOR y)"
  apply (simp only: word_eq_rbl_eq Let_def rbl_word_plus rbl_word_xor)
  apply (simp add: rbl_plus_carry_chain carry_word_def)
  apply (rule nth_equalityI, simp_all)
  apply (simp add: nth_rev xor3_def word_bl.Abs_inverse)
  apply blast
  done

(* the silly cw AND cw part is to stop the let_alt simproc removing the let-binding *)
lemma word_plus_carry_chain:
  fixes x :: "('a :: len) word"
  shows "x + y = (let xnm = x; ynm = y; cw = carry_word xnm ynm False in (xnm XOR ynm) XOR (cw AND cw))"
  apply (simp add: Let_def carry_word_eq_xor)
  apply (simp add: word_eq_iff word_ops_nth_size word_size)
  apply blast
  done

lemmas word_minus_carry_chain = HOL.trans[OF diff_conv_add_uminus word_plus_carry_chain]

lemma rev_bl_order_carry_chain:
  "length xs = length ys \<Longrightarrow>
    rev_bl_order F xs ys = (if xs = [] then F else
        carry (\<not> (last (carry_chain (zip xs (map Not ys)) (\<not> F)))) (\<not> (last xs)) (last ys))"
  apply (induct arbitrary: F rule: list_induct2)
   apply (simp_all add: rev_bl_order_simps zip_eq_Nil_iff)
  apply (intro impI conjI, simp_all)
   apply (simp add: carry_def)
   apply blast
  apply (rule arg_cong[where f="\<lambda>x. carry x _ _"])
  apply simp
  apply (rule arg_cong[where f="last"])
  apply (rule arg_cong[where f="carry_chain _"])
  apply (simp add: carry_def)
  apply blast
  done

lemma rev_bl_order_to_bl_carry_chain:
  fixes x :: "('a :: len) word"
  shows "rev_bl_order F (rev (to_bl x)) (rev (to_bl y)) =
    carry (\<not> msb (carry_word x (NOT y) (\<not> F))) (\<not> msb x) (msb y)"
  apply (simp add: rev_bl_order_carry_chain last_rev word_msb_alt)
  apply (simp add: hd_rev[symmetric] zip_eq_Nil_iff Let_def)
  apply (simp add: carry_word_def word_bl.Abs_inverse bl_word_not rev_map hd_map)
  done

(* the silly cw AND cw part is to stop the let_alt simproc removing the let-binding *)
lemma word_le_carry_chain:
  fixes x :: "('a :: len) word"
  shows "(x \<le> y) = (let xnm = x; ynm = NOT y; cw = carry_word xnm ynm False in
    carry (~ msb (cw AND cw)) (~ msb xnm) (~ msb ynm))"
  by (simp add: word_le_rbl rev_bl_order_to_bl_carry_chain Let_def word_ops_msb)

lemmas word_less_carry_chain = word_le_carry_chain[THEN arg_cong[where f=Not],
    simplified linorder_not_le]

lemma map_last_flip_to_xor:
  fixes x :: "('a :: len) word"
  shows "map_last Not (rev (to_bl x)) = rev (to_bl (x XOR (1 << (size x - 1))))"
  apply (rule nth_equalityI, simp_all add: word_size map_last_def)
  apply (simp add: nth_append nth_rev to_bl_nth nth_tl word_size word_ops_nth_size)
  apply (simp add: nth_shiftl last_conv_nth rev_nth to_bl_nth flip: shiftl_1)
  apply (intro conjI impI arg_cong2[where f="test_bit"], simp_all add: word_size)
  done

lemma word_sle_xor_eq_le[simplified word_size]:
  "(x <=s y) = (x XOR (1 << (size x - 1)) \<le> y XOR (1 << (size x - 1)))"
  by (simp add: word_sle_rbl word_le_rbl map_last_flip_to_xor word_size)

lemma word_sless_xor_eq_le[simplified word_size]:
  "(x <s y) = (x XOR (1 << (size x - 1)) < y XOR (1 << (size x - 1)))"
  by (simp add: word_sless_rbl word_less_rbl map_last_flip_to_xor word_size)

lemma minus_one_nat_case:
  "(n - 1) = (case n of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> j)"
  by (simp split: nat.split)

lemma carry_chain_nth:
  "i < length xs \<Longrightarrow> nth (carry_chain xs F) i = (case i of 0 \<Rightarrow> F | Suc j \<Rightarrow>
    carry (fst (nth xs j)) (snd (nth xs j)) (nth (carry_chain xs F) j))"
proof (induct i arbitrary: F xs)
  case 0
  then show ?case
    by (cases xs; simp)
next
  case (Suc i)
  from Suc.prems show ?case
    apply (cases xs; simp)
    apply (simp add: Suc.hyps)
    apply (simp split: nat.split)
    done
qed

lemma carry_word_nth:
  fixes x :: "('a :: len) word"
  shows "i < LENGTH ('a) \<Longrightarrow>
    test_bit (carry_word x y F) i = (case i of 0 \<Rightarrow> F | Suc j \<Rightarrow> carry (test_bit x j) (test_bit y j)
        (test_bit (carry_word x y F) j))"
  apply (simp add: carry_word_def test_bit_of_bl carry_chain_nth)
  apply (simp add: test_bit_bl word_size carry_word_def split: nat.split)
  apply (simp add: word_bl.Abs_inverse)
  done

lemma carry_word_eq_eq:
  fixes x :: "('a :: len) word"
  shows "(carry_word x y F = z) = (\<forall>i \<in> set (upt 0 (LENGTH ('a))).
    (case i of 0 \<Rightarrow> F | Suc j \<Rightarrow> carry (test_bit x j) (test_bit y j) (test_bit z j)) = test_bit z i)"
  apply (rule iffI)
   apply (clarsimp simp: carry_word_nth)
  apply (simp add: word_eq_iff Ball_def)
  apply (rule allI, induct_tac n)
   apply (intro impI, drule spec, drule(1) mp)
   apply (simp add: carry_word_nth)
  apply (intro impI, drule spec, drule(1) mp)
  apply (simp add: carry_word_nth[where i="Suc _"])
  done

lemma upt_Suc_left:
  "upt (Suc i) j = (if j = 0 then [] else map Suc (upt i (j - 1)))"
  by (cases j, simp_all add: map_Suc_upt)

lemma carry_word_eq_rbl:
  fixes x :: "('a :: len) word"
  shows "(carry_word x y F = z) = (F = test_bit z 0 \<and> (\<forall>(i, (xb, yb)) \<in> set (zip (upt 1 (LENGTH ('a)))
        (zip (rev (to_bl x)) (rev (to_bl y)))).
    carry xb yb (test_bit z (case i of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> j)) = test_bit z i))"
  apply (simp only: carry_word_eq_eq)
  apply (subst upt_rec[where i=0])
  apply (simp add: upt_Suc_left del: set_upt)
  apply (simp add: all_set_conv_all_nth, simp add: Ball_def)
  apply (intro conj_cong arg_cong[where f=All] ext imp_cong refl)
  apply (frule order_less_le_trans[OF _ diff_le_self])
  apply (simp add: test_bit_bl word_size)
  done

lemma word_if_add_let:
  "(if P then (x :: ('a :: len0) word) else y) = (let switch = P in id If switch x y)"
  by simp

lemma rbl_plus_simp_let:
  "rbl_plus cin (x # xs) (y # ys) =
    xor3 x y cin # (let c = carry x y cin in rbl_plus c xs ys)"
  by (simp add: rbl_plus_def)

lemma rev_bl_order_simp_let:
  "rev_bl_order F (x # xs) (y # ys) =
    (let xv = x; yv = y in rev_bl_order ((yv \<and> \<not> xv) \<or> ((yv \<or> \<not> xv) \<and> F)) xs ys)"
  by (simp add: rev_bl_order_simps)

lemma let_cons_expand:
  "(let xs = b # bs in f xs) = (let hd_x = b; tl_xs = bs in f (hd_x # tl_xs))"
  by simp

lemma let_word_rbl:
  "(let x = w in f x) = (let bs = rev (to_bl w) in f (of_bl (rev bs)))"
  by simp

lemma let_reassoc:
  "(let x = (let y = vy in f y) in g x) = (let y = vy; x = f y in g x)"
  by simp

lemma rev_to_bl_of_bl[OF refl, simplified word_size]:
  "w = of_bl xs \<Longrightarrow> rev (to_bl w) = takefill False (size w) (rev xs)"
  by (simp add: word_rev_tf word_size)

lemma lift_let:
  "f (let x = v in g x) = (let x = v in f (g x))"
  by simp

lemmas lift_let_binop = lift_let[where f="\<lambda>x. f x y" for f y] lift_let[where f="f x" for f x]

lemma takefill_last_empty_let:
  "takefill_last z n [] = (let bit = z in replicate n bit)"
  by (simp add: takefill_last_simps)

lemmas takefill_last_simps2 = takefill_last_simps(1-2) takefill_last_empty_let

lemma rbl_succ2_simp_let:
  "rbl_succ2 b (x # xs) = (b \<noteq> x) # (let c = x \<and> b in rbl_succ2 c xs)"
  by (simp_all add: rbl_succ2_def)

lemmas rbl_succ2_simps2 = rbl_succ2_simps(1) rbl_succ2_simp_let

lemmas bitwise_let_lifts =
    lift_let[where f="case_prod f" for f]
    lift_let[where f="case_list y f" for y f]
    lift_let_binop[where f="(=)"]
    lift_let[where f="map f" for f]
    lift_let_binop[where f="zip"]
    lift_let[where f="drop n" for n]
    lift_let[where f="foldr f" for f]
    lift_let[where f="takefill f n" for f n]
    lift_let[where f="drop_nonempty v n" for v n]
    lift_let_binop[where f="rev_bl_order f" for f]
    lift_let_binop[where f="list_all2 f" for f]
    lift_let[where f="rbl_succ2 x" for x]
    lift_let_binop[where f="rbl_plus cin" for cin]
    lift_let_binop[where f="append"]
    lift_let[where f="takefill_last z n" for z n]

lemmas logic_let_lifts =
    lift_let_binop[where f="(\<longrightarrow>)"]
    lift_let_binop[where f="(\<and>)"]
    lift_let_binop[where f="(\<or>)"]
    lift_let_binop[where f="(=)"]
    lift_let[where f="Not"]

lemmas imp_to_id = id_apply[where x="(\<longrightarrow>)", THEN fun_cong, THEN fun_cong, symmetric]

lemma let_eqI:
  "(\<And>x. v = x \<Longrightarrow> f x) \<Longrightarrow> let x = v in f x"
  by simp

lemma let_eq_impI:
  "(\<And>x. v = x \<longrightarrow> P x) \<Longrightarrow> let x = v in P x"
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

fun count_no_bv (t :: ts) tab = let
    val ts = case t of
        f $ x => f :: x :: ts
      | Abs (_, _, t) => t :: ts
      | _ => ts
    val tab = if has_bv t then tab
        else Termtab.map_default (t, 0) (fn i => i + 1) tab
  in count_no_bv ts tab end
  | count_no_bv [] tab = tab

val sym_def = @{thm Let_def[symmetric]}

fun add_let_conv ctxt nm x ct = let
    val abs = Thm.lambda_name (nm, x) ct
  in Drule.infer_instantiate ctxt [(("f", 0), abs), (("s", 0), x)] sym_def end

fun let_gather_dup_conv_1 ctxt f ct = let
    val count = count_no_bv [Thm.term_of ct] Termtab.empty
    val xs = Termtab.dest count
      |> filter (fn (_, j) => j >= 2)
      |> map fst
      |> filter (not o is_atom)
      |> filter f
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

ML \<open>
structure BW_Alt = struct

open Word_Bitwise_Tac

val no_split_ss =
  simpset_of (put_simpset HOL_ss \<^context>
        delsimprocs [@{simproc let_simp}]
    |> Splitter.del_split @{thm if_split});

val init_ss = simpset_of (put_simpset HOL_basic_ss \<^context> addsimps
   @{thms word_eq_rbl_eq word_le_carry_chain word_less_carry_chain
        word_sle_xor_eq_le word_sless_xor_eq_le})

val expand_word_eq_sss = map simpset_of [
   put_simpset no_split_ss \<^context> addsimps
    @{thms rbl_word_plus rbl_word_and rbl_word_or rbl_word_not
                                rbl_word_neg bl_word_sub rbl_word_xor
                                rbl_word_cat rbl_word_slice rbl_word_scast
                                rbl_word_ucast rbl_shiftl rbl_shiftr rbl_sshiftr
                                rbl_word_if_let lift_let[where f=to_bl]
                                lift_let[where f=rev]
                                rev_to_bl_of_bl rev_rev_ident},
   put_simpset no_split_ss \<^context> addsimps
    @{thms to_bl_numeral to_bl_neg_numeral to_bl_0 rbl_word_1},
   put_simpset no_split_ss \<^context> addsimps
    @{thms rev_rev_ident rev_replicate rev_map to_bl_upt word_size minus_one_nat_case}
          addsimprocs [word_len_simproc],
   put_simpset no_split_ss \<^context> addsimps
    @{thms split_conv replicate.simps list.simps
                                zip_Cons_Cons zip_Nil drop_Suc_Cons drop_0 drop_Nil
                                foldr.simps zip.simps(1) takefill_Suc_Cons
                                takefill_Suc_Nil takefill.Z rbl_succ2_simps2
                                rbl_plus_simp_let rbl_plus_simps(2-)
                                rev_bin_to_bl_simps append.simps
                                takefill_last_simps2 drop_nonempty_simps
                                rev_bl_order_simp_let rev_bl_order_simps(1)
                                bitwise_let_lifts let_cons_expand
                                ball_simps nat.simps
                                let_reassoc[where f="_ :: _ \<Rightarrow> _ list" for f]
                                Let_def[where f="\<lambda>_. []"]}
          addsimprocs [expand_upt_simproc,
                       @{simproc let_atom},
                       nat_get_Suc_simproc 1
                         [\<^term>\<open>replicate\<close>, \<^term>\<open>takefill x\<close>,
                          \<^term>\<open>drop\<close>, \<^term>\<open>bin_to_bl\<close>,
                          \<^term>\<open>takefill_last x\<close>,
                          \<^term>\<open>drop_nonempty x\<close>,
                          @{term \<open>nat.case_nat x y\<close>}]],
    put_simpset no_split_ss \<^context> addsimps @{thms xor3_simps carry_simps if_bool_simps
            Let_def[where s=True] Let_def[where s=False] One_nat_def id_apply}
        addsimprocs [@{simproc let_alt}]
  ]

val is_word = can Word_Lib.dest_wordT o fastype_of

fun rev_mp_prems_tac pred ctxt = SUBGOAL (fn (t, i) => let
    val prems = Logic.strip_assums_hyp t
    val idx = find_index (fn t => can HOLogic.dest_Trueprop t andalso pred t) prems
  in
    if idx = ~1 then all_tac
    else EVERY' [rotate_tac idx, eresolve_tac ctxt @{thms rev_mp}, rotate_tac (~ idx),
        rev_mp_prems_tac pred ctxt] i
  end)

fun let_to_imp_step ctxt = FIRST'
  [resolve_tac ctxt @{thms let_eq_impI},
   CHANGED o Let_Alt.let_to_top_tac ctxt,
   CHANGED o Let_Alt.let_gather_dup_tac ctxt is_word]

fun let_to_imp_tac ctxt = TRY o REPEAT_ALL_NEW (let_to_imp_step ctxt)

fun core_tacs ctxt = [
    (CHANGED o safe_full_simp_tac (put_simpset init_ss ctxt addsimprocs [@{simproc let_alt}])),
    rev_mp_prems_tac (exists_Const (fn (s, _) =>
        s = @{const_name to_bl} orelse s = @{const_name carry_word})) ctxt,
    safe_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
        @{thms word_plus_carry_chain word_minus_carry_chain word_if_add_let}),
    let_to_imp_tac ctxt,
    safe_simp_tac (put_simpset HOL_basic_ss ctxt addsimps
        @{thms id_apply carry_word_eq_rbl msb_nth word_bw_same}),
    safe_simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms imp_to_id}),
    safe_simp_tac (put_simpset init_ss ctxt)] @
    map (fn ss => safe_simp_tac (put_simpset ss ctxt)) expand_word_eq_sss

fun core_tac ctxt = foldr1 (op THEN_ALL_NEW) (core_tacs ctxt)

fun expand_tac ctxt = core_tac ctxt
    THEN_ALL_NEW safe_full_simp_tac
        (put_simpset no_split_ss ctxt addsimps @{thms Let_def})

fun lift_tac ctxt = core_tac ctxt
    THEN_ALL_NEW simp_tac
        (put_simpset HOL_basic_ss ctxt addsimps @{thms logic_let_lifts})
    THEN_ALL_NEW (TRY o DETERM o REPEAT_ALL_NEW (resolve_tac ctxt @{thms let_eqI}))

end
\<close>

method_setup let_dup_word =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (Let_Alt.let_gather_dup_tac ctxt BW_Alt.is_word 1))\<close>
  "gather repeated word terms using let-binding"

method_setup word_bitwise =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (BW_Alt.expand_tac ctxt 1))\<close>
  "decomposer for word equalities and inequalities into bit propositions"

method_setup word_bitwise_eq =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (BW_Alt.lift_tac ctxt 1))\<close>
  "decomposer for word equalities and inequalities into bit propositions,
    lifting shared booleans to variables"

lemma test_bit_is_slice_check:
  fixes x :: "('a :: len) word"
  shows "test_bit x n = (Word.slice n x = (1 :: 1 word))"
  by (simp add: word_eq_iff nth_slice)

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
