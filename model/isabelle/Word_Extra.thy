(*<*)
(* Author: Kyndylan Nienhuis *)
(* Author: Thomas Bauereiss *)
theory Word_Extra
imports 
  Main
  "HOL-Library.Word"
  "HOL-Eisbach.Eisbach_Tools"
  "Word_Lib.Reversed_Bit_Lists"
begin
(*>*)

section \<open>Library for machine words\<close>

text \<open>We first prove lemmas about integers, then about definitions that create words (such as
@{const mask} and @{const max_word}), then about definitions that manipulate words of the same size
(such as \<open>NOT\<close>, \<open>AND\<close>, \ldots), then about definitions that manipulate words of different sizes
(such as @{const ucast}, @{const slice}) and finally we define a bit-wise order over words.\<close>

subsection \<open>Integers\<close>

text \<open>We start by proving lemmas about integers that can later be lifted to machine words.\<close>

subsubsection \<open>Power of two difference\<close>

lemma mod_power_self:
  fixes x :: "'a::euclidean_semiring_cancel"
  shows "x ^ n mod x = (if n = 0 then 1 mod x else 0)"
by (induct n) simp_all

lemma int_power_of_two_difference:
  assumes "n \<le> m"
  shows "(2 ^ m - 1) AND NOT (2 ^ n - 1) = (2::int) ^ m - 2 ^ n"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = push_bit n (mask (m - n))"
    using assms
    by (simp add: push_bit_int_def mask_int_def field_simps power_add[symmetric])
  also have "\<dots> = ?lhs"
    apply (rule bit_eqI)
    apply (simp add: bit_push_bit_iff_int bit_mask_iff bit_and_iff mask_int_def[symmetric] bit_not_int_iff)
    apply auto
    done
  finally show ?thesis by simp
qed

subsection \<open>Words to and from integers\<close>

lemma uint_less [simp]:
  fixes x :: "'a::len word"
  shows "uint x \<le> 2 ^ LENGTH('a)"
  using unsigned_less[where w=x, THEN order.strict_implies_order] .

subsection \<open>Bit operations on integers and naturals\<close>

lemmas nat_take_bit_simp[simp] = nat_take_bit_eq[unfolded take_bit_nat_def]

subsection \<open>Exhaustive enumeration of small words\<close>

lemma UNIV_word:
  "(UNIV :: ('a :: len) word set) = word_of_nat ` set [0 ..< 2 ^ LENGTH('a)]"
  by (auto simp add: word_unat.univ unats_def)

lemmas exhaustive_word = UNIV_word[THEN eqset_imp_iff, simplified UNIV_I simp_thms]

lemma exhaustive_1_word:
  fixes x :: "1 word"
  obtains "x = 0"
        | "x = 1"
  using exhaustive_word[of x]
  by (auto simp add: upt_rec)

lemma exhaustive_2_word:
  fixes x :: "2 word"
  obtains "x = 0"
        | "x = 1"
        | "x = 2"
        | "x = 3"
  using exhaustive_word[of x]
  by (auto simp add: upt_rec)

lemma exhaustive_3_word:
  fixes x :: "3 word"
  obtains "x = 0"
        | "x = 1"
        | "x = 2"
        | "x = 3"
        | "x = 4"
        | "x = 5"
        | "x = 6"
        | "x = 7"
  using exhaustive_word[of x]
  by (auto simp add: upt_rec)

lemma exhaustive_4_word:
  fixes x :: "4 word"
  obtains "x = 0" | "x = 1" | "x = 2" | "x = 3" | "x = 4" | "x = 5" | "x = 6" | "x = 7" | "x = 8"
    | "x = 9" | "x = 10" | "x = 11" | "x = 12" | "x = 13" | "x = 14" | "x = 15"
  using exhaustive_word[of x]
  by (auto simp add: upt_rec)

lemma word1_eq_1_neq_0:
  fixes w :: "1 word"
  shows "(w = 1) \<longleftrightarrow> \<not>(w = 0)"
  by (cases w rule: exhaustive_1_word) auto

lemma of_bl_eq_1_word[simp]:
  "of_bl [b] = (1 :: 1 word) \<longleftrightarrow> b"
  "of_bl [b] = (0 :: 1 word) \<longleftrightarrow> \<not>b"
  by (cases b) auto

subsection \<open>Masks\<close>

text \<open>We see @{const max_word} as a special case of @{const mask}.\<close>

lemma min_uint_length:
  fixes x :: "'a::len word"
  shows "min (uint x) (2 ^ LENGTH('a) - 1) = uint x"
proof -
  have "uint x \<le> 2 ^ LENGTH('a) - 1" by simp
  from min_absorb1[OF this]
  show ?thesis .
qed

corollary min_length_uint:
  fixes x :: "'a::len word"
  shows "min (2 ^ LENGTH('a) - 1) (uint x) = uint x"
using min_uint_length[where x=x]
by simp

lemma min_unat_length:
  fixes x :: "'a::len word"
  shows "min (unat x) (2 ^ LENGTH('a) - 1) = unat x"
proof -
  have "unat x \<le> 2 ^ LENGTH('a) - 1"
    using word_le_nat_alt[THEN iffD1, OF max_word_max[where n=x]]
    by (simp add: unat_minus_one_word)
  from min_absorb1[OF this]
  show ?thesis .
qed

corollary min_length_unat:
  fixes x :: "'a::len word"
  shows "min (2 ^ LENGTH('a) - 1) (unat x) = unat x"
using min_unat_length[where x=x]
by simp

lemma add_and_masks:
  fixes x :: "('a :: len) word"
  shows
  "NO_MATCH (a AND mask b) x \<Longrightarrow>
    (x + y) AND mask n = ((x AND mask n) + y) AND mask n"
  "NO_MATCH (a AND mask b) y \<Longrightarrow>
    (x + y) AND mask n = (x + (y AND mask n)) AND mask n"
  "NO_MATCH (a AND mask b) x \<Longrightarrow>
    (x - y) AND mask n = ((x AND mask n) - y) AND mask n"
  "NO_MATCH (a AND mask b) y \<Longrightarrow>
    (x - y) AND mask n = (x - (y AND mask n)) AND mask n"
  by (simp_all add: mask_eqs)

subsection \<open>@{const max_word}\<close>

text \<open>These lemmas are not a corollary of a corresponding lemma about @{const mask}.\<close>

lemma max_word_le [simp]:
  shows "(max_word \<le> x) = (x = max_word)"
using antisym
by auto

lemma max_word_less [simp]:
  shows "(x < max_word) = (x \<noteq> max_word)"
    and "(max_word < x) = False"
unfolding not_le[THEN sym]
by simp_all

subsection \<open>Negation\<close>

lemma word_not_alt:
  fixes x :: "'a::len word"
  shows "NOT x = max_word - x"
  by (simp add: not_eq_complement)

lemma uint_not:
  fixes x :: "'a::len word"
  shows "uint (NOT x) = uint (max_word::'a::len word) - uint x"
  using uint_minus_simple_alt[THEN iffD1, OF max_word_max]
  by (auto simp: word_not_alt)

corollary unat_not:
  fixes x :: "'a::len word"
  shows "unat (NOT x) = unat (max_word::'a::len word) - unat x"
  unfolding uint_not  unat_eq_nat_uint
  using nat_diff_distrib' 
  by auto

lemma uint_not_mask:
  shows "uint (NOT (mask n)::'a::len word) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ LENGTH('a) - 2 ^ n)"
  by (auto simp: uint_not uint_mask_eq mask_int_def simp flip: minus_1_eq_mask[symmetric])

subsection \<open>Conjunction\<close>
        
lemma conj_outside_absorb [simp]:
  fixes x y :: "'a::len word"
  shows "x AND y AND x = x AND y"
  by (simp add: ring_bit_operations_class.bit.conj_commute)

subsection \<open>XOR\<close>

lemma word_xor_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n"
  shows "x XOR mask n = NOT x"
  using assms
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

subsection \<open>Addition and bitwise operations\<close>

lemma word_plus_is_or:
  fixes x y :: "('a :: len) word"
  shows "x AND y = 0 \<Longrightarrow> x + y = x OR y"
  using word_plus_and_or[of x y]
  by simp

subsection \<open>Lower and upper bits\<close>

(* Perhaps we should create a definition for the lower and upper bits. The only annoying thing
is that I'd like the parameter for the upper bits to specify how many lower bits are cleared, 
while intuitively it specifies how many upper bits are retained.*)

abbreviation(input)
  word_mask :: "nat \<Rightarrow> ('a :: len) word"
  where
  "word_mask \<equiv> mask"

lemma mask_and_mask [simp]:
  shows "word_mask n AND mask m = mask (min m n)"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma not_mask_and_not_mask [simp]:
  shows "NOT (word_mask n) AND NOT (mask m) = NOT (mask (max m n))"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma mask_and_not_mask [simp]:
  assumes "n \<le> m"
  shows "(word_mask n) AND NOT (mask m) = 0"
  using assms
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

corollary not_mask_and_mask [simp]:
  assumes "m \<le> n"
  shows "NOT (word_mask n) AND (mask m) = 0"
using assms 
unfolding ring_bit_operations_class.bit.conj_commute[of "NOT _"]
by simp

lemma word_and_mask_and_word_and_not_mask [simp]:
  shows "(x AND (word_mask n)) AND (y AND NOT (mask n)) = 0"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

corollary word_and_not_mask_and_word_and_mask [simp]:
  shows "(x AND NOT (word_mask n)) AND (y AND (mask n)) = 0"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma word_and_not_mask_or_word_and_mask [simp]:
  shows "(x AND NOT (word_mask n)) OR (x AND (mask n)) = x"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

corollary word_and_mask_or_word_and_not_mask [simp]:
  shows "(x AND (word_mask n)) OR (x AND NOT (mask n)) = x"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma word_and_not_mask_plus_word_and_mask [simp]:
  shows "(x AND NOT (word_mask n)) + (x AND (mask n)) = x"
using word_plus_and_or[where x="x AND NOT (mask n)" and y="x AND (mask n)"]
by simp

corollary word_and_mask_plus_word_and_not_mask [simp]:
  shows "(x AND (word_mask n)) + (x AND NOT (mask n)) = x"
using trans[OF ab_semigroup_add_class.add.commute
               word_and_not_mask_plus_word_and_mask] .

corollary word_minus_word_and_mask [simp]:
  shows "x - (x AND (word_mask n)) = (x AND NOT (mask n))"
by (simp add: diff_eq_eq)

corollary word_minus_word_and_not_mask [simp]:
  shows "x - (x AND NOT (word_mask n)) = (x AND (mask n))"
by (simp add: diff_eq_eq)

corollary word_and_mask_minus_word [simp]:
  shows "(x AND word_mask n) - x = - (x AND NOT (mask n))"
by (simp add: diff_eq_eq)

corollary word_and_not_mask_minus_word [simp]:
  shows "(x AND NOT (word_mask n)) - x = - (x AND (mask n))"
by (simp add: diff_eq_eq)

lemma uint_word_and_not_mask_plus_uint_word_and_mask [simp]:
  shows "uint (x AND NOT (mask n)) + uint (x AND (mask n)) = uint x"
proof -
  have "x AND NOT (mask n) \<le> (x AND NOT (mask n)) + (x AND (mask n))"
    using word_and_le2
    by auto
  from uint_plus_simple[OF this]
  show ?thesis by simp
qed

corollary uint_word_and_mask_plus_uint_word_and_not_mask [simp]:
  shows "uint (x AND (mask n)) + uint (x AND NOT (mask n)) = uint x"
using trans[OF ab_semigroup_add_class.add.commute
               uint_word_and_not_mask_plus_uint_word_and_mask] .

corollary unat_word_and_not_mask_plus_unat_word_and_mask [simp]:
  shows "unat (x AND NOT (mask n)) + unat (x AND (mask n)) = unat x"
  unfolding unat_eq_nat_uint
  by (subst nat_add_distrib[symmetric], simp_all)

lemma word_and_mask [simp]:
  fixes x :: "('a :: len) word"
  assumes "len_of TYPE('a) \<le> m"
  shows "(x AND mask m) = x"
proof (intro word_eqI impI, simp only: word_size)
  fix i
  assume len_of_'a: "i < len_of TYPE('a)"
  hence "i < m" using assms by simp
  thus "(x AND mask m) !! i = x !! i"
    using len_of_'a
    by (simp add: nth_ucast word_ao_nth word_size) 
qed

lemma uint_and_mask:
  fixes x :: "'a::len word"
  shows "uint (x AND mask n) = uint x mod 2 ^ (min n LENGTH('a))"
  unfolding uint_and uint_mask_eq mask_int_def AND_mod
  by (simp add: min.commute)

lemma unat_and_mask:
  fixes x :: "'a::len word"
  shows "unat (x AND mask n) = unat x mod 2 ^ (min n LENGTH('a))"
unfolding unat_eq_nat_uint uint_and_mask
using nat_mod_distrib nat_power_eq
by simp

lemma word_and_not_mask [simp]:
  fixes x :: "('a :: len) word"
  assumes "len_of TYPE('a) \<le> m"
  shows "(x AND NOT (mask m)) = 0"
using assms
by (intro word_eqI)
   (auto simp: word_size word_ops_nth_size)

lemma uint_and_not_mask:
  fixes x :: "'a::len word"
  shows "uint (x AND NOT (mask n)) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ n * (uint x div 2 ^ n))"
proof -
  have "uint (x AND NOT (mask n)) + uint (x AND mask n) = uint x"
    by simp
  hence "uint (x AND NOT (mask n)) = uint x - uint (x AND mask n)"
    by arith
  also have "... = uint x - uint x mod 2 ^ min n LENGTH('a)"
    by (simp add: uint_and_mask)
  also have "... = uint x mod 2 ^ min n LENGTH('a) + 
                   2 ^ min n LENGTH('a) * (uint x div 2 ^ min n LENGTH('a)) -
                   uint x mod 2 ^ min n LENGTH('a)"
    using mod_mult_div_eq[where a="uint x" and b="2 ^ min n LENGTH('a)"]
    by auto
  also have "... = 2 ^ min n LENGTH('a) * (uint x div 2 ^ min n LENGTH('a))"
    by arith
  also have "... = (if LENGTH('a) \<le> n then 0 else 2 ^ n * (uint x div 2 ^ n))"
    proof (cases "LENGTH('a) \<le> n")
      case True
      hence [simp]: "min n LENGTH('a) = LENGTH('a)"
        by simp
      have "uint x div 2 ^ LENGTH('a) = 0"
        using div_pos_pos_trivial
        by auto
      thus ?thesis
        using True by simp
    qed auto
  finally show ?thesis .
qed

corollary unat_and_not_mask:
  fixes x :: "'a::len word"
  shows "unat (x AND NOT (mask n)) = 
         (if LENGTH('a) \<le> n then 0 else 2 ^ n * (unat x div 2 ^ n))"
unfolding unat_eq_nat_uint uint_and_not_mask
by (simp add: nat_div_distrib nat_mult_distrib nat_power_eq)

lemma uint_and_mask_plus_uint_and_mask_less:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint (x AND mask n) + uint (y AND mask n) < 2 ^ (n + 1)"
proof -
  have [simp]: "min n LENGTH('a) = n"
    using assms by auto
  have "0 < (2::'a word) ^ n"
    by (simp add: assms word_2p_lem word_size)
  from uint_2p[OF this]
  have [simp]: "uint ((2::'a word) ^ n) = 2 ^ n" .
  show ?thesis
    using and_mask_less'[OF assms, where w=x]
    using and_mask_less'[OF assms, where w=y]
    unfolding word_less_def
    by simp
qed

corollary uint_and_mask_plus_uint_and_mask_less_size:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint (x AND mask n) + uint (y AND mask n) < 2 ^ LENGTH('a)"
proof -
  have "n + 1 \<le> LENGTH('a)"
    using assms by auto
  hence "(2::int) ^ (n + 1) \<le> 2 ^ LENGTH('a)"
    using one_le_numeral power_increasing by blast
  thus ?thesis
    using uint_and_mask_plus_uint_and_mask_less[where x=x and y=y, OF assms]
    by simp
qed

corollary plus_word_and_mask_no_wrap:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "(x AND mask n) \<le> (x AND mask n) + (y AND mask n)"
unfolding no_olen_add
using uint_and_mask_plus_uint_and_mask_less_size[OF assms]
by simp

corollary uint_plus_word_and_mask [simp]:
  fixes x y :: "'a::len word"
  assumes "n < LENGTH('a)"
  shows "uint ((x AND mask n) + (y AND mask n)) =  
         uint (x AND mask n) + uint (y AND mask n)"
using uint_and_mask_plus_uint_and_mask_less_size[OF assms]
unfolding uint_add_lem .

lemma uint_word_and_mask_plus_word_and_not_mask:
  shows "uint ((x AND mask n) + (y AND NOT (mask n))) = 
         uint (x AND mask n) + uint (y AND NOT (mask n))"
proof (cases "n \<le> LENGTH('a)")
  case True
  hence [simp]: "min n LENGTH('a) = n"
    by simp
  note [simp] = dvd_imp_mod_0[OF le_imp_power_dvd[where a="2::int", OF True]]
  have [simp]: "((2::int) ^ LENGTH('a) - 1) div 2 ^ n = 2 ^ LENGTH('a) div 2 ^ n - 1"
    using div_add1_eq[where a="2 ^ LENGTH('a)" and b="-1::int" and c="2 ^ n"]
    using zdiv_mult_self[where a="-1" and n=1 and m="2 ^ n"]
    using True
    by (auto simp: m1mod2k div_eq_minus1)
  have x: "uint (x AND mask n) < 2 ^ n"
    unfolding uint_and_mask
    by simp
  have "uint y \<le> 2 ^ LENGTH('a) - 1"
    by auto
  from zdiv_mono1[where b="2 ^ n", OF this]
  have "uint (y AND NOT (mask n)) \<le> 2 ^ n * (2 ^ LENGTH('a) div 2 ^ n - 1)"
    unfolding uint_and_not_mask
    using True
    by auto
  also have "... = 2 ^ LENGTH('a) - 2 ^ n"
    unfolding right_diff_distrib zmde
    by simp
  finally have "uint (x AND (mask n)) + uint (y AND NOT (mask n)) < 2 ^ LENGTH('a)"
    using x by auto
  from uint_add_lem[THEN iffD1, OF this]
  show ?thesis .
qed simp

corollary uint_word_and_not_mask_plus_word_and_mask:
  shows "uint ((x AND NOT (mask n)) + (y AND mask n)) = 
         uint (x AND NOT (mask n)) + uint (y AND mask n)"
by (simp add: uint_word_and_mask_plus_word_and_not_mask add.commute)

corollary unat_word_and_mask_plus_word_and_not_mask:
  shows "unat ((x AND mask n) + (y AND NOT (mask n))) = 
         unat (x AND mask n) + unat (y AND NOT (mask n))"
unfolding unat_eq_nat_uint uint_word_and_mask_plus_word_and_not_mask
using nat_add_distrib 
by auto

corollary unat_word_and_not_mask_plus_word_and_mask:
  shows "unat ((x AND NOT (mask n)) + (y AND mask n)) = 
         unat (x AND NOT (mask n)) + unat (y AND mask n)"
by (simp add: unat_word_and_mask_plus_word_and_not_mask add.commute)

lemma not_mask_eq_plus:
  fixes x :: "('a :: len) word"
  shows "x + (y AND NOT (mask n)) AND NOT (mask n) = (x AND NOT (mask n)) + (y AND NOT (mask n))"
proof -
  have "x + (y AND NOT (mask n)) AND NOT (mask n) = x + y - (y AND mask n) AND NOT (mask n)"
    by (simp add: add_diff_eq[THEN sym])
  also have "... = x + y - (y AND mask n) - ((x + y - (y AND mask n)) AND mask n)"
    by simp
  also have "... = x + y - (y AND mask n) - (x AND mask n)"
    unfolding mask_eqs
    by simp
  also have "... = x - (x AND mask n) + y - (y AND mask n)"
    by simp
  also have "... = (x AND NOT (mask n)) + (y AND NOT (mask n))"
    by simp
  finally show ?thesis .
qed

corollary not_mask_eq_plus_commuted:
  shows "(x AND NOT (word_mask n)) + y AND NOT (mask n) = (x AND NOT (mask n)) + (y AND NOT (mask n))"
using not_mask_eq_plus[where x=y and y=x]
by (simp add: add.commute)

lemma not_mask_eq_minus:
  fixes x :: "('a :: len) word"
  shows "x - (y AND NOT (mask n)) AND NOT (mask n) = (x AND NOT (mask n)) - (y AND NOT (mask n))"
proof -
  have "x - (y AND NOT (mask n)) AND NOT (mask n) = x - y + (y AND mask n) AND NOT (mask n)"
    by (simp add: diff_diff_eq2[THEN sym] diff_add_eq)
  also have "... = x - y + (y AND mask n) - (x - y + (y AND mask n) AND mask n)"
    by simp
  also have "... = x - y + (y AND mask n) - (x AND mask n)"
    unfolding mask_eqs
    by simp
  also have "... = (x AND NOT (mask n)) - (y AND NOT (mask n))"
    by (simp add: diff_diff_eq2[THEN sym] diff_add_eq)
  finally show ?thesis .
qed

find_theorems "_ AND mask _ = _" "_ \<le> _"

lemma word_plus_and_mask:
  fixes x y :: "'a::len word"
  assumes le: "(x AND mask n) + (y AND mask n) \<le> mask n"
  shows "x + y AND mask n = (x AND mask n) + (y AND mask n)"
  using and_mask_eq_iff_le_mask[THEN iffD2, OF le]
  by (simp add: mask_eqs)

corollary word_plus_and_not_mask:
  fixes x y :: "'a::len word"
  assumes "(x AND mask n) + (y AND mask n) \<le> mask n"
  shows "x + y AND NOT (mask n) = (x AND NOT (mask n)) + (y AND NOT (mask n))"
proof -
  have "x + y AND NOT (mask n) = (x + y) - (x + y AND mask n)"
    by simp
  also have "... = (x + y) - ((x AND mask n) + (y AND mask n))"
    unfolding word_plus_and_mask[OF assms] ..
  also have "... = (x -  (x AND mask n)) + (y - (y AND mask n))"
    using add_diff_eq diff_add_eq diff_diff_add
    by (metis (no_types, hide_lams))
  also have "... = (x AND NOT (mask n)) + (y AND NOT (mask n))"
    by simp
  finally show ?thesis .
qed

lemma mask_minus_word_and_mask [simp]:
  fixes x :: "'a::len word"
  shows "mask n - (x AND mask n) = NOT x AND mask n"
proof -
  have "mask n - (x AND mask n) = (mask n - (x AND mask n)) AND mask n"
    proof (cases "n < LENGTH('a)")
      case True
      have "mask n - (x AND mask n) < 2 ^ n"
        using word_sub_le[OF word_and_le1[where y=x and a="mask n"]]
        using and_mask_less'[where w=max_word, OF True]
        by simp
      from less_mask_eq[OF this]
      show ?thesis by simp
    qed simp
  also have "... = NOT x AND mask n"
    unfolding word_not_alt
    using mask_eqs(8)[where a="max_word" and b=x and n=n]
    by simp
  finally show ?thesis .
qed

lemma word_power_of_two_difference:
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(2::'a::len word) ^ m - 2 ^ n = mask m AND NOT (mask n)"
proof (cases "m \<le> LENGTH('a)")
  case True
  have "(2::'a::len word) ^ m - 2 ^ n = word_of_int (2 ^ m - 2 ^ n)"
    unfolding word_sub_wi word_of_int_2p[THEN sym] int_word_uint
    using mod_power_lem assms True
    by (auto simp: word_of_int_minus)
  also have "... = word_of_int ((2 ^ m - 1) AND NOT (2 ^ n - 1))"
    using assms int_power_of_two_difference
    by simp
  also have "... = word_of_int (2 ^ m - 1) AND NOT (word_of_int (2 ^ n - 1))"
    unfolding word_and_def word_not_def wils1
    by simp
  also have "... = mask m AND NOT (mask n)"
    unfolding mask_2pm1 shiftl_1 word_sub_wi word_of_int_2p[THEN sym] int_word_uint 
    using mod_power_lem assms True
    by (auto simp: word_of_int_minus)
  finally show ?thesis by simp
next
  case False
  then obtain m' where m_def: "m = LENGTH('a) + m'"
    unfolding not_le using less_imp_add_positive by auto
  have [simp]: "(2::'a::len word) ^ m = 0"
    unfolding word_of_int_2p[THEN sym] m_def power_add word_of_int_2p_len
    by simp
  have "NOT (mask n::'a word) = - (2 ^ n)"
    unfolding mask_2pm1 shiftl_1 word_sub_wi bwsimps int_not_def 
    by (auto simp: wi_hom_syms)
  thus ?thesis 
    unfolding mask_2pm1 shiftl_1
    by simp
qed

lemma word_and_mask_xor_mask [simp]:
  shows "x AND word_mask n XOR mask n = (NOT x) AND mask n"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma word_and_mask_and_mask [simp]:
  shows "(x AND word_mask n) AND mask m = x AND mask (min n m)"
  by (intro word_eqI) (auto simp: word_size word_ops_nth_size)

lemma and_shiftl_not_mask [simp]:
  assumes "m \<le> n"
  shows "(x << n) AND NOT (word_mask m) = x << n"
using assms
by (intro word_eqI)
   (auto simp: word_size word_ops_nth_size nth_shiftl)

lemma word_and_mask_shiftl_eq_shiftl[simp]:
  assumes "i + j \<ge> LENGTH('a)"
  shows "x AND (mask i :: 'a::len word) << j = x << j"
  using assms by (intro word_eqI) (auto simp: nth_shiftl word_ao_nth word_size)

lemma word_and_mask_0_iff_not_testbits: "(w AND word_mask n) = 0 \<longleftrightarrow> (\<forall>i < n. \<not>w !! i)"
  using test_bit_size[of w] by (auto simp: word_ao_nth word_eq_iff word_size)

lemma word_of_int_shiftl:
  "word_of_int (shiftl x y) = shiftl (word_of_int x) y"
  by (auto simp: word_eq_iff nth_shiftl)

lemma shiftl_mask_eq_0:
  "m \<le> n \<Longrightarrow> (x << n) AND word_mask m = 0"
  by (simp add: word_eq_iff word_ops_nth_size nth_shiftl word_size)

lemma test_bit_plus_mask_zero:
  assumes high_eq: "x AND NOT (word_mask k) = y AND NOT (mask k)"
    and low: "z AND mask k = 0"
    and test: "n < k \<longrightarrow> test_bit x n = test_bit y n"
  shows "test_bit (x + z) n = test_bit (y + z) n"
proof -
  have P: "(x + z) AND (NOT (mask k)) = (y + z) AND (NOT (mask k))"
    apply (simp only: word_minus_word_and_mask[symmetric])
    apply (simp add: word_plus_and_mask low word_and_le1 high_eq)
    done

  have Q: "(x + z) AND mask k = x AND mask k"
    by (simp add: word_plus_and_mask low word_and_le1)

  have R: "(y + z) AND mask k = y AND mask k"
    by (simp add: word_plus_and_mask low word_and_le1)

  from P Q R test show ?thesis
    apply (simp add: word_eq_iff)
    apply (drule spec[where x=n])+
    apply (simp add: word_ops_nth_size word_size)
    apply ((intro iffI; elim impCE; (frule test_bit_size)?), simp_all add: word_size)
     apply auto
    done
qed

subsection \<open>@{const slice}\<close>

text \<open>We see @{const ucast} as a special case of @{const slice}.\<close>

lemma slice_zero [simp]:
  shows "slice 0 x = ucast x"
by (intro word_eqI) (simp add: nth_slice nth_ucast word_size)

lemma slice_beyond_length [simp]:
  fixes x :: "'a::len word"
  assumes len: "LENGTH('a) \<le> n"
  shows "slice n x = 0"
proof (intro word_eqI impI notI, clarsimp simp: word_size)
  fix m
  assume "m < LENGTH('b)" "slice n x !! m"
  hence "x !! (m + n)"
    by (simp add: nth_slice)
  from test_bit_size[OF this]
  have "m + n < LENGTH('a)"
    by (simp add: word_size)
  thus False
    using len by auto
qed

lemma slice_not:
  fixes x :: "'a::len word"
  shows "(slice n (NOT x)::'b::len word) = NOT (slice n x) AND mask (LENGTH('a) - n)"
proof (intro word_eqI iffI impI, unfold word_size)
  fix i
  assume length: "i < LENGTH('b)"
  assume "(slice n (NOT x)::'b word) !! i"
  hence "(NOT x) !! (i + n)"
    by (simp add: nth_slice)
  with test_bit_size[OF this]
  show "(NOT (slice n x::'b word) AND mask (LENGTH('a) - n)) !! i"
    using length
    by (auto simp: word_size nth_slice word_ops_nth_size)
next
  fix i
  assume "i < LENGTH('b)"
     and "(NOT (slice n x::'b word) AND mask (LENGTH('a) - n)) !! i"
  thus "(slice n (NOT x)::'b word) !! i"
    by (auto simp: word_size nth_slice word_ops_nth_size)
qed

corollary ucast_not:
  fixes x :: "'a::len word"
  shows "(ucast (NOT x)::'b::len word) = NOT (ucast x) AND mask LENGTH('a)"
using slice_not[where n=0]
by simp

lemma slice_or:
  shows "slice n (x OR y) = slice n x OR slice n y"
by (intro word_eqI)
   (auto simp: word_size word_ao_nth nth_slice)
    
lemma ucast_or:
  shows "ucast (x OR y) = ucast x OR ucast y"
using slice_or[where n=0]
by simp
(* Direct proof: 
unfolding ucast_eq uint_or bitOR_word.abs_eq[THEN sym] .. *)

lemma slice_and:
  shows "slice n (x AND y) = slice n x AND slice n y"
by (intro word_eqI)
   (auto simp: word_size word_ao_nth nth_slice)
    
lemma ucast_and:
  shows "ucast (x AND y) = ucast x AND ucast y"
using slice_and[where n=0]
by simp
(* Direct proof: 
unfolding ucast_eq uint_and bitAND_word.abs_eq[THEN sym] .. *)

lemma slice_xor:
  fixes x y :: "'a::len word"
  shows "(slice n (x XOR y)::'b::len word) = slice n x XOR slice n y"
proof (intro word_eqI iffI impI, unfold word_size)
  fix m
  assume "m < LENGTH('b)" 
     and "slice n (x XOR y) !! m"
  hence "(x XOR y) !! (m + n)"
    by (simp add: nth_slice)
  with test_bit_size[OF this]
  have "x !! (m + n) \<noteq> y !! (m + n)"
    by (simp add: word_ops_nth_size word_size)
  thus "((slice n x XOR slice n y)::'b::len word) !! m"
    using `m < LENGTH('b)`
    by (simp add: nth_slice word_ops_nth_size word_size)
next
  fix m
  assume "m < LENGTH('b)" 
     and "((slice n x XOR slice n y)::'b::len word) !! m"
  hence *: "x !! (m + n) \<noteq> y !! (m + n)"
    by (simp add: nth_slice word_ops_nth_size word_size)
  hence "m + n < LENGTH('a)"
    by (cases "x !! n") 
       (auto dest: test_bit_size simp: word_size)
  thus "(slice n (x XOR y)::'b::len word) !! m"
    using * `m < LENGTH('b)`
    by (simp add: nth_slice word_ops_nth_size word_size)
qed

lemma ucast_xor:
  fixes x y :: "'a::len word"
  shows "(ucast (x XOR y)::'b::len word) = ucast x XOR ucast y"
using slice_xor[where n=0]
by simp

(* lemma slice_word_of_int:
  assumes "n + LENGTH('a) \<le> LENGTH('b)"
  shows "(slice n (word_of_int m::'b::len word)::'a::len word) = 
         word_of_int (m div 2 ^ n)"
using assms
by (intro word_eqI)
   (auto simp: word_size nth_slice word_of_int zdiv_int bin_nth_div) *)

lemma slice_word_of_int:
  shows "slice n (word_of_int m::'a::len word) = 
         word_of_int (m div 2 ^ n) AND mask (LENGTH('a) - n)"
by (intro word_eqI)
   (auto simp: word_size nth_slice word_ao_nth drop_bit_int_def[symmetric] bit_drop_bit_eq add.commute)
  
corollary ucast_word_of_int:
  shows "ucast (word_of_int m::'a::len word) = 
         word_of_int m AND mask LENGTH('a)"
using slice_word_of_int[where n=0] 
by simp

corollary slice_of_nat:
  shows "slice n (of_nat m::'a::len word) = 
         of_nat (m div 2 ^ n) AND mask (LENGTH('a) - n)"
using slice_word_of_int[where m="int m" and n=n]
using zdiv_int[where a=m and b="2 ^ n", THEN sym]
by simp
  
corollary ucast_of_nat:
  shows "(ucast (of_nat m::'b::len word)::'a::len word) = 
         of_nat m AND mask LENGTH('b)"
using slice_of_nat[where n=0]
by simp

(* corollary
  fixes x :: "'a::len word"
  shows "slice n x = x div (2 ^ n)"
proof -
  have "slice n x = word_of_int (uint x div 2 ^ n) AND mask (LENGTH('a) - n)"
    using slice_word_of_int[where m="uint x" and n=n and 'a='a]
    by simp

  have "... = x div (2 ^ n)"
    unfolding word_div_def
    apply auto
oops *)

lemma slice_mask [simp]:
  shows "slice n (mask m::'a::len word) = mask (min m LENGTH('a) - n)"
by (intro word_eqI) (auto simp add: nth_slice word_size)
  
corollary ucast_mask [simp]:
  shows "ucast ((mask n)::'a::len word) = mask (min n LENGTH('a))"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

lemma slice_of_slice [simp]:
  shows "slice n (slice m x::'a::len word) = 
         slice (n + m) x AND mask (LENGTH('a) - n)"
by (intro word_eqI)
   (auto simp add: word_size nth_slice word_ao_nth add.assoc)

corollary slice_ucast [simp]:
  shows "slice n (ucast x::'a::len word) = 
         (slice n x) AND mask (LENGTH('a) - n)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

corollary ucast_slice [simp]:
  shows "ucast (slice n x::'a::len word) = 
         (slice n x) AND mask LENGTH('a)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

corollary ucast_ucast [simp]:
  shows "ucast (ucast x::'b::len word) = 
         ucast x AND mask LENGTH('b)"
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

lemma slice_word_and_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) + n \<le> m"
  shows "(slice n (x AND mask m)::'b::len word) = slice n x"
proof (intro word_eqI impI, simp only: word_size)
  fix i
  assume len: "i < LENGTH('b)"
  hence "i + n < m" using assms by simp
  thus "(slice n (x AND mask m)::'b word) !! i = (slice n x::'b word) !! i"
    using len test_bit_size[where w=x and n="i + n"]
    by (auto simp add: nth_slice word_ao_nth word_size) 
qed

corollary ucast_word_and_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) \<le> m"
  shows "(ucast (x AND mask m)::'b::len word) = ucast x"
using assms
unfolding slice_zero[THEN sym]
by (simp del: slice_zero)

subsection \<open>@{const ucast}\<close>

text \<open>These lemmas are not a corollary of a corresponding lemma about @{const slice}.\<close>

lemma zero_less_ucast [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(0 < (ucast x::'b::len word)) = (0 < x)"
unfolding ucast_eq word_less_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma one_less_ucast [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(1 < (ucast x::'b::len word)) = (1 < x)"
unfolding ucast_eq word_less_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma one_le_ucast [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(1 \<le> (ucast x::'b::len word)) = (1 \<le> x)"
unfolding ucast_eq word_le_def word_ubin.eq_norm bintr_uint[OF assms]
by auto

lemma ucast_up_eq [simp]:
  fixes x y :: "'a::len word"
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "((ucast x::'b::len word) = (ucast y)) = (x = y)"
proof 
  assume ucast: "(ucast x::'b word) = ucast y"
  show "x = y"
    proof (intro word_eqI impI, unfold word_size)
      fix n
      assume "n < LENGTH('a)"
      thus "x !! n = y !! n"
        using test_bit_cong[where x=n, OF ucast] assms
        by (auto simp: nth_ucast)
    qed
qed simp

lemma uint_ucast [simp]:
  fixes x :: "'a::len word"
  shows "uint (ucast x::'b::len word) = 
         uint (x AND mask LENGTH('b))"
proof (intro bin_nth_eq_iff[THEN iffD1] ext)
  fix i
  show "bin_nth (uint (ucast x::'b word)) i = 
        bin_nth (uint (x AND mask LENGTH('b))) i"
    using test_bit_size[where w=x and n=i]
    by (auto simp add: test_bit_def'[THEN sym] 
                       nth_ucast 
                       word_ao_nth 
                       word_size)
qed

corollary unat_ucast [simp]:
  fixes x :: "'a::len word"
  shows "unat ((ucast x :: ('b :: len) word)) = 
         unat (x AND mask (len_of TYPE('b)))"
unfolding unat_eq_nat_uint
by simp

lemma ucast_max_word [simp]:
  shows "ucast (max_word::'a::len word) = mask LENGTH('a)"
by (intro word_eqI) (simp add: word_size nth_ucast)

lemma and_ucast_mask [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n"
  shows "(ucast x::'b::len word) AND mask n = ucast x"
proof (intro word_eqI impI iffI, unfold word_size)
  fix m
  assume "m < LENGTH('b)" "(ucast x::'b word) !! m"
  hence "x !! m"
    by (simp add: nth_ucast)
  from test_bit_size[OF this]
  have "m < n"
    using assms 
    unfolding word_size 
    by simp
  thus "((ucast x::'b word) AND mask n) !! m"
    using `m < LENGTH('b)` `x !! m`
    by (simp add: word_size nth_ucast word_ao_nth)
qed (simp add: nth_ucast word_ao_nth)

(* lemma ucast_max_word [simp]:
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (max_word::'a::len word)::'b::len word) = max_word"
using assms
by (intro word_eqI) (simp add: word_size nth_ucast) *)

declare word_cat_id [simp]

lemma ucast_word_cat [simp]:
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "(ucast (word_cat w w'::'b::len word)::'a::len word) = word_cat w w'"
unfolding ucast_eq word_cat_def 
unfolding word_ubin.eq_norm 
using assms
by (simp add: wi_bintr del: nat_take_bit_simp)

lemma ucast_shiftr:
  shows "(ucast (x >> n) :: ('b :: len) word) = slice n x"
by (intro word_eqI)
   (simp add: word_size nth_slice nth_ucast nth_shiftr)

lemma ucast_shiftl:
  fixes x :: "'a::len word"
  shows "ucast (x << n) = ucast (x AND mask (LENGTH('a) - n)) << n"
by (intro word_eqI) (auto simp: nth_ucast nth_shiftl word_ao_nth word_size)

lemma ucast_plus_down:
  fixes x y :: "'a ::len word"
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (x + y)::'b::len word) = ucast x + ucast y"
proof -
  have "(2::int) ^ LENGTH('b) dvd 2 ^ LENGTH('a)"
    using le_imp_power_dvd[OF assms, where a="2::int"] 
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis
    using assms mod_mod_cancel
    unfolding ucast_eq uint_word_ariths
    unfolding word_uint.norm_eq_iff[THEN sym] wi_hom_syms[THEN sym]
    by simp
qed

lemma ucast_plus_up:
  fixes x y :: "'a ::len word"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "(ucast (x + y)::'b::len word) = (ucast x + ucast y) AND mask (LENGTH('a))"
proof -
  have "LENGTH('a) \<le> LENGTH('b)"
    using assms by simp
  from le_imp_power_dvd[OF this, where a="2::int"] 
  have "(2::int) ^ LENGTH('a) dvd 2 ^ LENGTH('b)"
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis  
    unfolding ucast_eq uint_word_ariths and_mask_mod_2p wi_hom_syms[THEN sym] uint_word_of_int
    unfolding word_uint.norm_eq_iff[THEN sym]  
    by auto
qed

lemma ucast_minus_down:
  fixes x y :: "'a ::len word"
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (x - y)::'b::len word) = ucast x - ucast y"
proof -
  have "(2::int) ^ LENGTH('b) dvd 2 ^ LENGTH('a)"
    using le_imp_power_dvd[OF assms, where a="2::int"] 
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis
    using assms mod_mod_cancel
    unfolding ucast_eq uint_word_ariths
    unfolding word_uint.norm_eq_iff[THEN sym] wi_hom_syms[THEN sym]
    by simp
qed

lemma ucast_minus_up:
  fixes x y :: "'a ::len word"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "(ucast (x - y)::'b::len word) = (ucast x - ucast y) AND mask (LENGTH('a))"
proof -
  have "LENGTH('a) \<le> LENGTH('b)"
    using assms by simp
  from le_imp_power_dvd[OF this, where a="2::int"] 
  have "(2::int) ^ LENGTH('a) dvd 2 ^ LENGTH('b)"
    by simp
  from mod_mod_cancel[OF this]
  show ?thesis  
    unfolding ucast_eq uint_word_ariths and_mask_mod_2p wi_hom_syms[THEN sym] uint_word_of_int
    unfolding word_uint.norm_eq_iff[THEN sym]  
    by auto
qed

lemma uint_ucast_plus_ucast [simp]:
  fixes x :: "'a::len word"
    and y :: "'b::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "LENGTH('b) < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + ucast y) = uint x + uint y"
proof -
  have x: "uint x < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt2p[of x]] assms
    by auto
  have y: "uint y < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt2p[of y]] assms
    by auto
  have "(2::int) * 2 ^ (LENGTH('c) - 1) = 2 ^ (Suc (LENGTH('c) - 1))"
    by (rule power_Suc[THEN sym])
  also have "... = 2 ^ LENGTH('c)"
    by auto
  finally have "uint x + uint y < 2 ^ LENGTH('c)"
    using add_strict_mono[OF x y]
    by auto
  hence *: "uint (ucast x :: 'c word) + uint (ucast y :: 'c word) < 2 ^ LENGTH('c)"
    using assms by simp
  show ?thesis
    using uint_add_lem[THEN iffD1, OF *]
    using assms
    by simp
qed

lemma uint_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + 1) = uint x + 1"
    and "uint (1 + (ucast x :: 'c::len word)) = 1 + uint x"
using assms 
using uint_ucast_plus_ucast[where x=x and y="(1::1 word)" and 'c='c]
using uint_ucast_plus_ucast[where x="(1::1 word)" and y=x and 'c='c]
by auto

corollary unat_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "unat ((ucast x :: 'c::len word) + 1) = unat x + 1"
    and "unat (1 + (ucast x :: 'c::len word)) = 1 + unat x"
using assms
unfolding unat_eq_nat_uint
by (simp_all add: Suc_nat_eq_nat_zadd1[symmetric] add.commute)

corollary ucast_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "1 < LENGTH('c)"
  shows "(ucast ((ucast x :: 'c::len word) + 1)::'b::len word) = ucast x + 1"
    and "(ucast (1 + (ucast x :: 'c::len word))::'b::len word) = 1 + ucast x"
using arg_cong[where f="\<lambda>x. (word_of_int x::'b word)", OF uint_ucast_plus_one(1)[OF assms, of x]]
using arg_cong[where f="\<lambda>x. (word_of_int x::'b word)", OF uint_ucast_plus_one(2)[OF assms, of x]]
unfolding ucast_eq
by (auto simp: wi_hom_syms)

lemma uint_ucast_plus_ucast_plus_one [simp]:
  fixes x :: "'a::len word"
    and y :: "'b::len word"
  assumes "LENGTH('a) < LENGTH('c)"
      and "LENGTH('b) < LENGTH('c)"
  shows "uint ((ucast x :: 'c::len word) + ucast y + 1) = uint x + uint y + 1"
proof -
  have x: "uint x < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt2p[of x]] assms
    by auto
  have y: "uint y < 2 ^ (LENGTH('c) - 1)"
    using less_le_trans[OF uint_lt2p[of y]] assms
    by auto
  have "(2::int) * 2 ^ (LENGTH('c) - 1) = 2 ^ (Suc (LENGTH('c) - 1))"
    by (rule power_Suc[THEN sym])
  also have "... = 2 ^ LENGTH('c)"
    by auto
  finally have "uint x + uint y + 1 < 2 ^ LENGTH('c)"
    using zle_diff1_eq[THEN iffD2, OF x]
    using zle_diff1_eq[THEN iffD2, OF y]
    by auto
  hence "uint ((ucast x::'c word) + ucast y) + uint (1::'c word) < 2 ^ LENGTH('c)"
    using assms by simp
  from uint_add_lem[THEN iffD1, OF this]
  show ?thesis
    using assms by simp
qed

subsection \<open>@{const word_cat}\<close>

lemma nth_word_cat:
  fixes x :: "'a::len word"
    and y :: "'b::len word"
  shows "((word_cat x y)::'c::len word) !! n = 
         (n < len_of TYPE('c) \<and> 
          (if n < len_of TYPE('b) then y !! n else x !! (n - len_of TYPE('b))))"
  by (simp add: test_bit_cat word_size)

lemma word_cat_zero [simp]:
  shows "(word_cat 0 x) = ucast x"
using test_bit_size
by (intro word_eqI)
   (auto simp add: nth_word_cat nth_ucast word_size)

lemma word_cat_slice_zero [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('b) = n"
      and "LENGTH('c) = LENGTH('a) - n"
  shows "word_cat (slice n x::'c::len word) (0::'b::len word) = x AND NOT (mask n)"
using assms
by (intro word_eqI)
  (auto simp: word_size nth_word_cat nth_slice word_ops_nth_size)

lemma test_bit_len: "(x :: 'a::len word) !! n \<Longrightarrow> n < LENGTH('a)"
  by (auto simp: test_bit_bin)

lemma word_cat_shiftl_OR: "word_cat xs (ys :: 'y::len word) = (ucast xs << LENGTH('y)) OR ucast ys"
  using test_bit_len
  by (intro word_eqI) (auto simp: nth_word_cat word_ao_nth nth_shiftl nth_ucast)

subsection \<open>@{const shiftl}\<close>

lemma shiftl_zero [simp]:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n"
  shows "x << n = 0"
using assms
by (intro word_eqI) (simp add: word_size nth_shiftl)

lemma word_shiftl_add:
  "shiftl (x :: ('a :: len) word) (i + j) = shiftl (shiftl x i) j"
  by (simp add: shiftl_t2n power_add)

lemma word_shiftl_add_comm:
  "shiftl (x :: ('a :: len) word) (i + j) = shiftl (shiftl x j) i"
  by (simp add: shiftl_t2n power_add)

lemma word_and_mask_shiftl_eq:
  "(x AND word_mask i) << j = (x << j) AND mask (i + j)"
  by (auto simp add: word_eq_iff word_ops_nth_size nth_shiftl word_size)

lemma plus_minus_shiftl_distrib:
  fixes x :: "('a :: len) word"
  shows "(x + y) << i = (x << i) + (y << i)"
    "(x - y) << i = (x << i) - (y << i)"
  by (simp_all add: shiftl_t2n algebra_simps)

lemma shiftr_shiftl:
  "(shiftr x i) << j = (if i < j
    then (x AND NOT (word_mask i)) << j - i
    else shiftr (x AND NOT (mask i)) (i - j))"
  apply (simp add: word_eq_iff nth_shiftl nth_shiftr
        word_ops_nth_size word_ao_nth)
  apply (auto; frule test_bit_size; auto simp: word_ops_nth_size word_size)
  done

lemma shiftr_shiftl_alt:
  "(shiftr x i) << j = (if i \<le> j
    then (x AND NOT (word_mask i)) << j - i
    else shiftr (x AND NOT (mask i)) (i - j))"
  by (simp add: shiftr_shiftl)

subsection \<open>@{const scast}\<close>

lemma nth_scast:
  fixes w :: "'a::len word"
  shows "(scast w::'b::len word) !! n = 
         ((if n < LENGTH('a) - 1 then w !! n else w !! (LENGTH('a) - 1)) \<and> n < len_of TYPE('b))"
  using less_linear[of n "size w - 1"]
  by (auto simp: word_size test_bit_word_eq bit_word_scast_iff
    dest: bit_imp_le_length)

lemma scast_alt_def:
  fixes x :: "'a::len word"
  assumes "LENGTH('c) = LENGTH('a) + LENGTH('b)"
      and "m = LENGTH('a) - 1"
  shows "scast x = (word_cat (if x !! m then max_word else 0::'b::len word) x::'c::len word)"
  (is "?l = ?r")
proof (intro word_eqI impI, unfold word_size)
  fix n
  show "?l !! n = ?r !! n"
    by (cases "n = m")
       (auto simp: assms word_size nth_word_cat nth_scast 
             split: if_splits)
qed

lemma scast_scast_shiftl:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) + n \<le> LENGTH('b)"
  shows "(scast ((scast x::'b::len word) << n)::'c::len word) = scast x << n"
  (is "?l = ?r")
proof -
  have "LENGTH ('b) \<le> n \<longrightarrow> False"
    apply (clarsimp)
    apply (drule order_trans[rotated], rule assms)
    apply simp
    done

  then show ?thesis
    using assms
    by (intro word_eqI, simp add: nth_scast word_size nth_shiftl)
        auto
qed

lemma nth_scast2[OF refl]:
  "w2 = scast w \<Longrightarrow> w2 !! n =
    ((if n < size w then w !! n else msb w) \<and> n < size w2)"
  apply (simp add: nth_scast msb_nth)
  apply (cases "n = size w - 1", auto simp: word_size)
  done

lemma scast_eq_ucast_or:
  "scast x = ucast x OR (if msb x then NOT (mask (size x)) else 0)"
  apply (simp add: word_eq_iff word_ops_nth_size nth_ucast nth_scast2 word_size)
  apply (auto dest: test_bit_size simp: word_size)
  done

lemma scast_eq_ucast_plus:
  "scast x = ucast x + (if msb x then NOT (mask (size x)) else 0)"
  apply (subst word_plus_is_or)
   apply (simp add: word_eq_iff word_ops_nth_size nth_ucast word_size)
   apply (auto dest: test_bit_size simp: word_size)[1]
  apply (simp add: scast_eq_ucast_or)
  done

lemma scast_eq_ucast:
  "LENGTH ('b) \<le> LENGTH ('a) \<Longrightarrow>
    (scast (x :: ('a :: len) word) :: ('b :: len) word) = ucast x"
  apply (rule word_eqI)
  apply (clarsimp simp: nth_scast nth_ucast)
  apply (case_tac "n = size x - 1", simp_all add: word_size)
  done

subsection \<open>Upper bits and @{const slice}\<close>

lemma slice_eq_imp_and_not_mask_eq:
  fixes x y :: "'a::len word"
  assumes length: "LENGTH('a) \<le> LENGTH('b) + n"
      and slice: "(slice n x::'b::len word) = slice n y"
        (is "?sx = ?sy")
  shows "(x AND NOT (mask n)) = (y AND NOT (mask n))"
proof -
  have P: "i < LENGTH('a) \<Longrightarrow> ?sx !! (i - n) = ?sy !! (i - n)" for i
    using assms by simp

  show ?thesis
    using length
    apply (intro word_eqI impI, simp add: word_size)
    apply (frule P)
    apply (auto simp: word_size nth_slice word_ops_nth_size)
    done
qed

lemma and_not_mask_eq_imp_slice_eq:
  fixes x y :: "'a::len word"
  assumes length: "LENGTH('b) + n \<le> LENGTH('a)"
      and mask: "(x AND NOT (mask n)) = (y AND NOT (mask n))"
  shows "(slice n x::'b::len word) = slice n y"
proof (intro word_eqI impI, simp add: word_size)
  fix i
  assume "i < LENGTH('b)"
  thus "(slice n x::'b::len word) !! i = (slice n y::'b::len word) !! i"
    using length test_bit_cong[OF mask, where x="i + n"]
    by (auto simp: word_size nth_slice word_ops_nth_size)
qed

lemma eq_slice_eq_and_not_mask:
  fixes x y :: "'a::len word"
  assumes "LENGTH('a) = LENGTH('b) + n"
  shows "((slice n x::'b::len word) = slice n y) = 
         ((x AND NOT (mask n)) = (y AND NOT (mask n)))"
using assms 
using slice_eq_imp_and_not_mask_eq[where 'b='b and x=x and y=y and n=n]
using and_not_mask_eq_imp_slice_eq[where 'b='b and x=x and y=y and n=n]
by auto

subsection \<open>Lower bits and @{const ucast}\<close>

lemma eq_ucast_eq_and_mask:
  fixes x y :: "'a::len word"
  assumes "n = LENGTH('b)"
  shows "((ucast x::'b::len word) = ucast y) = 
         ((x AND mask n) = (y AND mask n))"
  using test_bit_size[of x] test_bit_size[of y]
  by (auto simp add: word_eq_iff word_size nth_ucast assms)

lemma ucast_minus:
  fixes x y :: "'a ::len word"
  shows "(ucast (x - y)::'b::len word) = (ucast x - ucast y) AND mask (LENGTH('a))"
  apply (cases "LENGTH('a) < LENGTH('b)")
   apply (simp_all add: ucast_minus_down ucast_minus_up)
  done

lemmas ucast_uminus = ucast_minus[where x=0, simplified]

lemma ucast_up_shiftr[OF refl, simplified is_up_def source_size target_size]:
  "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> uc (shiftr x i) = shiftr (uc x) i"
  apply (clarsimp simp: is_up_def source_size_def target_size_def)
  apply (auto simp add: word_eq_iff nth_shiftr nth_ucast word_size dest: test_bit_size)
  done

subsection \<open>Aligned inequalities\<close>

lemmas le_and_not_mask = neg_mask_mono_le

lemma le_right_and_not_mask:
  assumes "(ucast x::'b::len word) = 0"
      and "n = LENGTH('b)"
  shows "(x \<le> y AND NOT (mask n)) = (x \<le> y)"
proof
  assume "x \<le> y AND NOT (mask n)"
  thus "x \<le> y"
    using word_and_le2[where a=y and y="NOT (mask n)"]
    by auto
next
  have [simp]: "x AND mask n = 0"
    using assms eq_ucast_eq_and_mask[where x=x and y=0]
    by auto
  have [simp]: "x AND NOT (mask n) = x"
    using word_and_not_mask_plus_word_and_mask[where x=x and n=n]
    by simp
  assume "x \<le> y"
  from le_and_not_mask[where n=n, OF this]
  show "x \<le> y AND NOT (mask n)"
    by simp
qed

corollary less_left_and_not_mask:
  assumes "(ucast y::'b::len word) = 0"
      and "n = LENGTH('b)"
  shows "(x AND NOT (mask n) < y) = (x < y)"
using le_right_and_not_mask[where x=y and y=x, OF assms]
by auto

lemma word_and_mask_and_not_mask_size:
  fixes x :: "'a::len word"
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(x AND mask m) AND NOT (mask n) \<le> 2 ^ m - 2 ^ n"
unfolding word_power_of_two_difference[OF assms]
using le_and_not_mask[OF word_and_le1[where y=x and a="mask m"]]
by simp

corollary word_and_not_mask_and_mask_size:
  fixes x :: "'a::len word"
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
  shows "(x AND NOT (mask n)) AND mask m \<le> 2 ^ m - 2 ^ n"
using word_and_mask_and_not_mask_size[OF assms]
using ring_bit_operations_class.bit.conj_assoc ring_bit_operations_class.bit.conj_commute
by metis

subsection \<open>More inequalities\<close>

lemma word_sub_1_less:
  fixes x :: "('a :: len) word"
  shows "x \<noteq> 0 \<Longrightarrow> x - 1 < x"
  by (simp add: word_less_nat_alt measure_unat)

lemma word_le_nonzero_negate:
  fixes x :: "('a :: len) word"
  shows "x \<le> y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (- y) \<le> (- x)"
  using word_le_minus_mono[of "-1" "-1" "x - 1" "y - 1"]
    word_sub_1_less[of x] word_sub_1_less[of y]
  apply simp
  apply (erule meta_mp)
  apply (rule word_le_minus_mono, simp_all)
  apply (cases "y = 0", simp_all)
  done

lemma word_le_nonzero_negateI:
  fixes x :: "('a :: len) word"
  shows "- x \<le> - y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<le> x"
  by (drule word_le_nonzero_negate, simp+)

(*<*)
end
(*>*)
