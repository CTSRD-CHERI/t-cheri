theory Capabilities_lemmas
imports Capabilities
begin

lemma leq_cap_refl[simp, intro]:
  "leq_cap CC c c"
  by (simp add: leq_cap_def)

lemma leq_cap_tag_imp[intro]:
  assumes "leq_cap CC c c'"
    and "is_tagged_method CC c"
  shows "is_tagged_method CC c'"
  using assms
  by (auto simp: leq_cap_def)

lemma leq_bounds_trans:
  assumes "leq_bounds CC c c'" and "leq_bounds CC c' c''"
  shows "leq_bounds CC c c''"
  using assms
  by (auto simp: leq_bounds_def)

lemma leq_bools_iff:
  "leq_bools bs1 bs2 \<longleftrightarrow> (\<forall>n < length bs1. bs1 ! n \<longrightarrow> bs2 ! n) \<and> length bs2 = length bs1"
  by (induction bs1 bs2 rule: leq_bools.induct) (auto simp: nth_Cons split: nat.splits)

lemma leq_bools_refl[simp, intro]:
  "leq_bools b b"
  by (auto simp: leq_bools_iff)

lemma leq_perms_refl[simp, intro]:
  "leq_perms CC c c"
  unfolding leq_perms_def
  by auto

lemma leq_bools_trans:
  "leq_bools b b' \<Longrightarrow> leq_bools b' b'' \<Longrightarrow> leq_bools b b''"
  by (auto simp: leq_bools_iff)

lemma leq_perms_trans:
  assumes "leq_perms CC c c'" and "leq_perms CC c' c''"
  shows "leq_perms CC c c''"
  using assms
  unfolding leq_perms_def
  by (metis leq_bools_trans)

lemma leq_cap_trans:
  assumes "leq_cap CC c c'" and "leq_cap CC c' c''"
  shows "leq_cap CC c c''"
  using assms
  by (auto simp: leq_cap_def elim: leq_bounds_trans leq_perms_trans)

lemma address_range_upt[simp]: "address_range start len = [start ..< start + len]"
  by (induction len) (auto simp: address_range_def)

lemma get_mem_region_base_upt_top:
  "get_mem_region CC c = {get_base_method CC c ..< get_top_method CC c}"
  by (auto simp: get_mem_region_def)

lemma leq_cap_get_mem_region_subseteq:
  assumes "leq_cap CC c c'" and "is_tagged_method CC c"
  shows "get_mem_region CC c \<subseteq> get_mem_region CC c'"
  using assms
  by (auto simp: leq_cap_def leq_bounds_def get_mem_region_base_upt_top)

locale Capabilities =
  fixes CC :: "'cap Capability_class"
  assumes is_tagged_seal[simp]: "\<And>c t. is_tagged_method CC (seal_method CC c t) = is_tagged_method CC c"
    and is_tagged_unseal[simp]: "\<And>c. is_tagged_method CC (unseal_method CC c) = is_tagged_method CC c"
    and is_tagged_clear_global[simp]: "\<And>c. is_tagged_method CC (clear_global_method CC c) = is_tagged_method CC c"
    and is_tagged_cap_of_mem_bytes[simp]: "\<And>c bytes tag. cap_of_mem_bytes_method CC bytes tag = Some c \<Longrightarrow> is_tagged_method CC c \<longleftrightarrow> tag = B1"
begin

inductive_set derivable :: "'cap set \<Rightarrow> 'cap set" for C :: "'cap set" where
  Copy: "c \<in> C \<Longrightarrow> c \<in> derivable C"
| Restrict: "c' \<in> derivable C \<Longrightarrow> leq_cap CC c c' \<Longrightarrow> c \<in> derivable C"
| Unseal:
    "\<lbrakk>c' \<in> derivable C; c'' \<in> derivable C; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; is_sealed_method CC c'; permits_unseal_method CC c'';
      get_obj_type_method CC c' = get_cursor_method CC c'';
      get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     clear_global_unless CC (is_global_method CC c'') (unseal_method CC c') \<in> derivable C"
| Seal:
    "\<lbrakk>c' \<in> derivable C; c'' \<in> derivable C; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; \<not>is_sealed_method CC c';
      permits_seal_method CC c''; get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     seal_method CC c' (get_cursor_method CC c'') \<in> derivable C"
| SealEntry:
    "\<lbrakk>c' \<in> derivable C; is_tagged_method CC c';
      \<not>is_sealed_method CC c';
      is_sentry_method CC (seal_method CC c' otype) \<or> is_indirect_sentry CC (seal_method CC c' otype)\<rbrakk> \<Longrightarrow>
     seal_method CC c' otype \<in> derivable C"

lemma derivable_mono:
  assumes "C \<subseteq> C'"
  shows "derivable C \<subseteq> derivable C'"
proof
  fix c
  assume "c \<in> derivable C"
  then show "c \<in> derivable C'" using assms by induction (auto intro: derivable.intros)
qed

lemma cap_derivable_bounded_gteq:
  assumes c: "cap_derivable_bounded CC n C c"
    and m: "m \<ge> n"
  shows "cap_derivable_bounded CC m C c"
proof -
  from m obtain k where "m = n + k" using less_iff_Suc_add[of n m] by auto
  also have "cap_derivable_bounded CC (n + k) C c" using c by (induction k) (auto)
  finally show ?thesis .
qed

lemma derivable_refl: "C \<subseteq> derivable C" by (auto intro: derivable.intros)

lemma derivable_empty: "derivable {} = {}"
proof -
  { fix c
    assume "c \<in> derivable {}"
    then have "False"
      by induction auto
  }
  then show ?thesis by auto
qed

lemma derivable_union_subseteq_absorb:
  assumes "C' \<subseteq> derivable C"
  shows "derivable (C \<union> C') = derivable C"
proof
  show "derivable (C \<union> C') \<subseteq> derivable C"
  proof
    fix c
    assume "c \<in> derivable (C \<union> C')"
    then show "c \<in> derivable C" using assms by induction (auto intro: derivable.intros)
  qed
  show "derivable C \<subseteq> derivable (C \<union> C')" by (intro derivable_mono) auto
qed

lemma derivable_minus_subseteq: "derivable (C - C') \<subseteq> derivable C"
proof
  fix c
  assume "c \<in> derivable (C - C')"
  then show "c \<in> derivable C" by induction (auto intro: derivable.intros)
qed

lemma derivable_Int1_subset:
  "derivable (A \<inter> B) \<subseteq> derivable A"
  by (intro derivable_mono) auto

lemma derivable_Int2_subset:
  "derivable (A \<inter> B) \<subseteq> derivable B"
  by (intro derivable_mono) auto

lemma cap_derivable_iff_derivable: "cap_derivable CC C c \<longleftrightarrow> c \<in> derivable C"
proof
  assume "cap_derivable CC C c"
  then obtain n where c: "cap_derivable_bounded CC n C c" by (auto simp: cap_derivable_def)
  then show "c \<in> derivable C"
    by (induction CC \<equiv> CC n C c rule: cap_derivable_bounded.induct)
       (auto intro: derivable.intros)
next
  assume c: "c \<in> derivable C"
  then have "\<exists>n. cap_derivable_bounded CC n C c"
  proof (induction rule: derivable.induct)
    case (Copy c)
    then have "cap_derivable_bounded CC 0 C c" by auto
    then show ?case by blast
  next
    case (Restrict c' c)
    then obtain n where "cap_derivable_bounded CC n C c'" by auto
    then have "cap_derivable_bounded CC (Suc n) C c" using Restrict.hyps by auto
    then show ?case by blast
  next
    case (Unseal c' c'')
    then obtain n' n''
      where "cap_derivable_bounded CC n' C c'" and "cap_derivable_bounded CC n'' C c''"
      by blast
    then have "cap_derivable_bounded CC (max n' n'') C c'"
      and "cap_derivable_bounded CC (max n' n'') C c''"
      by (auto intro: cap_derivable_bounded_gteq)
    then have "cap_derivable_bounded CC (Suc (max n' n'')) C (clear_global_unless CC (is_global_method CC c'') (unseal_method CC c'))"
      using Unseal.hyps
      by auto
    then show ?case by blast
  next
    case (Seal c' c'')
    then obtain n' n''
      where "cap_derivable_bounded CC n' C c'" and "cap_derivable_bounded CC n'' C c''"
      by blast
    then have "cap_derivable_bounded CC (max n' n'') C c'"
      and "cap_derivable_bounded CC (max n' n'') C c''"
      by (auto intro: cap_derivable_bounded_gteq)
    then have "cap_derivable_bounded CC (Suc (max n' n'')) C (seal_method CC c' (get_cursor_method CC c''))"
      using Seal.hyps
      by auto
    then show ?case by blast
  next
    case (SealEntry c' otype)
    then obtain n where "cap_derivable_bounded CC n C c'"
      by blast
    then have "cap_derivable_bounded CC (Suc n) C (seal_method CC c' otype)"
      using SealEntry.hyps
      by auto
    then show ?case by blast
  qed
  then show "cap_derivable CC C c" by (simp add: cap_derivable_def)
qed

end

locale Capabilities_Bounds_Invariants = Capabilities +
  assumes base_seal_eq: "\<And>c otype. get_base_method CC (seal_method CC c otype) = get_base_method CC c"
    and top_seal_eq: "\<And>c otype. get_top_method CC (seal_method CC c otype) = get_base_method CC c"
    and base_clear_global_eq: "\<And>c cond. get_base_method CC (clear_global_unless CC cond c) = get_base_method CC c"
    and top_clear_global_eq: "\<And>c cond. get_top_method CC (clear_global_unless CC cond c) = get_base_method CC c"
begin

lemma derivable_base_leq_top:
  assumes "\<forall>c \<in> C. is_tagged_method CC c \<longrightarrow> get_base_method CC c \<le> get_top_method CC c"
  shows "\<forall>c \<in> derivable C. is_tagged_method CC c \<longrightarrow> get_base_method CC c \<le> get_top_method CC c"
proof (intro ballI impI)
  fix c
  assume "c \<in> derivable C" and "is_tagged_method CC c"
  then show "get_base_method CC c \<le> get_top_method CC c"
    using assms
    by (induction rule: derivable.induct)
       (auto simp: leq_cap_def leq_bounds_def base_seal_eq top_seal_eq base_clear_global_eq top_clear_global_eq)
qed

end

locale Capabilities_Invariant = Capabilities CC
  for CC :: "'cap Capability_class" +
  fixes cap_invariant :: "'cap \<Rightarrow> bool"
  assumes leq_cap_invariant: "\<And>c c'. cap_invariant c \<Longrightarrow> leq_cap CC c' c \<Longrightarrow> is_tagged_method CC c \<Longrightarrow> is_tagged_method CC c' \<Longrightarrow> cap_invariant c'"
    and seal_cap_invariant: "\<And>c otype. cap_invariant c \<Longrightarrow> is_tagged_method CC c \<Longrightarrow> cap_invariant (seal_method CC c otype)"
    and unseal_cap_invariant: "\<And>c. cap_invariant c \<Longrightarrow> is_tagged_method CC c \<Longrightarrow> cap_invariant (unseal_method CC c)"
    and clear_global_cap_invariant: "\<And>c. cap_invariant c \<Longrightarrow> is_tagged_method CC c \<Longrightarrow> cap_invariant (clear_global_method CC c)"
begin

lemma derivable_cap_invariant:
  assumes "c \<in> derivable C" and "is_tagged_method CC c"
    and "\<forall>c' \<in> C. is_tagged_method CC c' \<longrightarrow> cap_invariant c'"
  shows "cap_invariant c"
  using assms
  by (induction rule: derivable.induct)
     (auto intro: leq_cap_invariant seal_cap_invariant unseal_cap_invariant clear_global_cap_invariant
           simp: clear_global_unless_def)

end

end
