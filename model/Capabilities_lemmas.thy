theory Capabilities_lemmas
imports Capabilities
begin

locale Capabilities =
  fixes CC :: "'cap Capability_class"
  assumes is_tagged_set_tag[simp]: "\<And>c tag. is_tagged_method CC (set_tag_method CC c tag) = tag"
    and is_tagged_set_seal[simp]: "\<And>c s. is_tagged_method CC (set_seal_method CC c s) = is_tagged_method CC c"
    and is_tagged_set_obj_type[simp]: "\<And>c t. is_tagged_method CC (set_obj_type_method CC c t) = is_tagged_method CC c"
    and is_tagged_set_perms[simp]: "\<And>c p. is_tagged_method CC (set_perms_method CC c p) = is_tagged_method CC c"
    and is_tagged_cap_of_mem_bytes[simp]: "\<And>c bytes tag. cap_of_mem_bytes_method CC bytes tag = Some c \<Longrightarrow> is_tagged_method CC c \<longleftrightarrow> tag = B1"
begin

inductive_set derivable :: "'cap set \<Rightarrow> 'cap set" for C :: "'cap set" where
  Copy: "c \<in> C \<Longrightarrow> c \<in> derivable C"
| Restrict: "c' \<in> derivable C \<Longrightarrow> leq_cap CC c c' \<Longrightarrow> c \<in> derivable C"
| Unseal:
    "\<lbrakk>c' \<in> derivable C; c'' \<in> derivable C; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; is_sealed_method CC c'; permits_unseal_method CC c'';
      get_obj_type_method CC c' = get_cursor_method CC c''\<rbrakk> \<Longrightarrow>
     unseal CC c' (get_global_method CC c'') \<in> derivable C"
| Seal:
    "\<lbrakk>c' \<in> derivable C; c'' \<in> derivable C; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; \<not>is_sealed_method CC c'; permits_seal_method CC c''\<rbrakk> \<Longrightarrow>
     seal CC c' (get_cursor_method CC c'') \<in> derivable C"

lemma leq_cap_refl[simp, intro]:
  "leq_cap CC c c"
  by (simp add: leq_cap_def)

lemma leq_cap_tag_imp[intro]:
  assumes "leq_cap CC c c'"
    and "is_tagged_method CC c"
  shows "is_tagged_method CC c'"
  using assms
  by (auto simp: leq_cap_def)

lemma address_range_upt[simp]: "address_range start len = [start ..< start + len]"
  by (induction len) (auto simp: address_range_def)

lemma get_mem_region_base_upt_top:
  "get_mem_region CC c = {get_base_method CC c ..< get_top_method CC c}"
  by (auto simp: get_mem_region_def)

lemma leq_cap_get_mem_region_subseteq:
  assumes "leq_cap CC c c'" and "is_tagged_method CC c"
  shows "get_mem_region CC c \<subseteq> get_mem_region CC c'"
  using assms
  by (auto simp: leq_cap_def get_mem_region_base_upt_top)

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
    then have "cap_derivable_bounded CC (Suc (max n' n'')) C (unseal CC c' (get_global_method CC c''))"
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
    then have "cap_derivable_bounded CC (Suc (max n' n'')) C (seal CC c' (get_cursor_method CC c''))"
      using Seal.hyps
      by auto
    then show ?case by blast
  qed
  then show "cap_derivable CC C c" by (simp add: cap_derivable_def)
qed

end

end
