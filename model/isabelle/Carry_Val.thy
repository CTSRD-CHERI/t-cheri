theory Carry_Val

imports "HOL-Library.Bit_Operations"
  "HOL-Library.Word"

begin

definition
  carry_val :: "('a :: semiring_bit_operations) \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
  where
  "carry_val x y c = (x + y + (if c then 1 else 0)) XOR (x XOR y)"

lemma carry_val_even:
  "even (carry_val x y c) = (\<not> c)"
proof -
  have "odd (carry_val x y c) = c"
    by (simp only: carry_val_def bit_0[symmetric] bit_xor_iff, simp)
  thus ?thesis
    by blast
qed

definition carry :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where "carry a b c = ((a \<and> (b \<or> c)) \<or> (b \<and> c))"

lemmas xor_div_2 = drop_bit_xor[where n="Suc 0", simplified drop_bit_Suc drop_bit_0, simplified]

lemma carry_val_int_div_2:
  fixes x :: int
  shows "(carry_val x y c) div 2 = carry_val (x div 2) (y div 2) (carry (odd x) (odd y) c)"
  apply (simp add: carry_val_def xor_div_2 carry_def)
  apply (intro conjI impI arg_cong2[where f="(XOR)"], simp_all, auto elim!: oddE evenE)
  done

lemma carry_val_int_bit_Suc:
  fixes x :: int
  shows "bit (carry_val x y c) (Suc i) =
    carry (bit x i) (bit y i) (bit (carry_val x y c) i)"
proof (induct i arbitrary: x y c rule: less_induct)
  case (less j)
  show ?case
    apply (simp add: bit_Suc carry_val_int_div_2)
    apply (cases j, simp_all add: carry_val_even)
    apply (simp add: less[where x="_ div _"])
    apply (simp add: bit_Suc carry_val_int_div_2)
    done
qed

lemma carry_val_word_eq_uint:
  fixes x :: "('a :: len) word"
  shows "carry_val x y c = word_of_int (carry_val (uint x) (uint y) c)"
  by (simp add: carry_val_def flip: bwsimps)

lemma carry_val_word_bit:
  fixes x :: "('a :: len) word"
  shows "i < LENGTH('a) \<Longrightarrow>
    bit (carry_val x y c) i = (case i of 0 \<Rightarrow> c
        | Suc j \<Rightarrow> carry (bit x j) (bit y j) (bit (carry_val x y c) j))"
  by (simp add: carry_val_word_eq_uint bit_word_of_int_iff carry_val_even
        carry_val_int_bit_Suc bit_uint_iff
    split: nat.split)

lemma carry_val_word_eq_eq:
  fixes x :: "('a :: len) word"
  shows "(carry_val x y c = z) = (\<forall>i \<in> set (upt 0 (LENGTH ('a))).
    (case i of 0 \<Rightarrow> c | Suc j \<Rightarrow> carry (bit x j) (bit y j) (bit z j)) = bit z i)"
  apply (rule iffI[OF _ bit_word_eqI])
   apply (clarsimp simp: carry_val_word_bit)
  apply (erule rev_mp[where P="_ < _"])
  apply (induct_tac n)
   apply (simp_all add: eq_commute[where b="bit z _"] carry_val_word_bit flip: bit_0)
  done

lemma carry_val_word_eq_eq_Suc:
  fixes x :: "('a :: len) word"
  shows "(carry_val x y c = z) = (bit z 0 = c \<and> (\<forall>i \<in> set (upt 0 (LENGTH ('a) - 1)).
    (carry (bit x i) (bit y i) (bit z i)) = bit z (Suc i)))"
proof -
  have set: "set [0..<LENGTH('a)] = insert 0 (Suc ` {0 ..< LENGTH('a) - 1})"
    by auto

  show ?thesis
    apply (simp only: carry_val_word_eq_eq set ball_simps nat.simps)
    apply auto
    done
qed

lemma arith_via_carry_val:
  "(x + y) = (let x_nm = x; y_nm = y; c = carry_val x_nm y_nm False in x_nm XOR y_nm XOR c)"
  "(x - y) = (let x_nm = x; y_inv_nm = NOT y; c = carry_val x_nm y_inv_nm True in x_nm XOR y_inv_nm XOR c)"
  "(- x) = (let x_inv_nm = NOT x; c = carry_val 0 x_inv_nm True in x_inv_nm XOR c)"
  by (simp_all add: carry_val_def ac_simps not_eq_complement)

lemma bit_carry_val_int_position_cong:
  fixes x :: int and x' :: int
  assumes x: "\<forall>j \<le> i. bit x j = bit x' j"
  assumes y: "\<forall>j \<le> i. bit y j = bit y' j"
  shows "bit (carry_val x y c) i = bit (carry_val x' y' c) i"
  apply (induct i rule: dec_induct[OF le0])
   apply (simp add: carry_val_even)
  apply (simp add: carry_val_int_bit_Suc x y)
  done

lemma word_le_eq_carry:
  fixes x :: "('a :: len) word"
  shows "(x \<le> y) = (let x_inv_nm = NOT x; y_nm = y; c = carry_val y_nm x_inv_nm True in
    carry (bit y_nm (size x - 1)) (bit x_inv_nm (size x - 1)) (bit c (size x - 1)))"
  (is "?lhs = ?rhs")
proof -
  have P: "bit (uint y - uint x) n \<Longrightarrow>
        n \<ge> size x \<longrightarrow> bit (uint y - uint x) (size x)" for n
    by (rule impI, erule(1) inc_induct)
      (simp add: arith_via_carry_val Let_def bit_not_iff bit_xor_iff bit_uint_iff
        carry_val_int_bit_Suc carry_def word_size)

  have eq_bit: "?lhs = (\<not> bit (uint y - uint x) (size x))"
    apply (simp add: uint_minus_simple_alt uint_word_arith_bintrs)
    apply (simp add: bit_eq_iff bit_take_bit_iff word_size)
    apply (auto dest: P simp: word_size)
    done

  note bit_carry_val_size_x = carry_val_int_bit_Suc[where i="size x - 1", simplified]
  note adj = bit_carry_val_int_position_cong[of n w w "NOT (uint x)" "uint (NOT x)" for n w]

  show ?thesis
    by (simp add: eq_bit Let_def arith_via_carry_val bit_not_iff bit_xor_iff
        bit_carry_val_size_x[simplified word_size] bit_uint_iff word_size
        carry_val_word_eq_uint bit_word_of_int_iff adj)
qed

lemma signed_take_bit_xor_eq:
  fixes x :: int
  shows "signed_take_bit n x = take_bit (Suc n) (xor x (2 ^ n)) - 2 ^ n"
  by (simp add: signed_take_bit_eq_take_bit_minus
        flip_bit_def[unfolded push_bit_of_1, symmetric]
        flip_bit_eq_if take_bit_unset_bit_eq take_bit_set_bit_eq
        unset_bit_eq[where k="take_bit _ _"] set_bit_eq[where k="take_bit _ _"]
        bit_take_bit_iff)

lemma word_sle_xor_eq_le[simplified word_size]:
  "(x <=s y) = (x XOR (push_bit (size x - 1) 1) \<le> y XOR (push_bit (size x - 1) 1))"
  apply (simp add: word_sle_eq sint_uint word_le_def signed_take_bit_xor_eq
        push_bit_of_1 word_size uint_xor)
  apply (simp add: uint_2p word_neq_0_conv[symmetric] bintr_uint)
  done

lemmas word_ineq_via_carry_val = word_le_eq_carry[unfolded word_size]
    linorder_not_le[of x, symmetric, unfolded word_le_eq_carry word_size]
    word_sle_xor_eq_le signed.not_le[symmetric]
  for x :: "('a :: len) word"

lemmas word_via_carry_val = arith_via_carry_val[of x] word_ineq_via_carry_val
  for x :: "('a :: len) word"

lemma word_bit_eq_iff:
  fixes x :: "('a :: len) word"
  shows "(x = y) = (\<forall>i \<in> set [0 ..< LENGTH('a)]. bit x i = bit y i)"
  by (intro iffI bit_word_eqI, simp_all)

end