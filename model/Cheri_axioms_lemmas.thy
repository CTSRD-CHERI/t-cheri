theory Cheri_axioms_lemmas
imports Capabilities_lemmas Cheri_axioms
begin

locale Capability_ISA = Capabilities CC
  for CC :: "'cap Capability_class" +
  fixes ISA :: "('cap, 'regval, 'instr, 'e) isa"

lemma reads_from_reg_at_idx_Some_iff[simp]:
  "reads_from_reg_at_idx i t = Some r \<longleftrightarrow> reads_from_reg (t ! i) = Some r \<and> i < length t"
  by (auto simp: reads_from_reg_at_idx_def bind_eq_Some_conv)

lemma reads_from_reg_SomeE[elim!]:
  assumes "reads_from_reg e = Some r"
  obtains v where "e = E_read_reg r v"
  using assms
  by (cases e) auto

lemma reads_from_reg_Some_iff:
  "reads_from_reg e = Some r \<longleftrightarrow> (\<exists>v. e = E_read_reg r v)"
  by (cases e) auto

lemma member_reads_reg_caps_at_idx_iff[simp]:
  "c \<in> reads_reg_caps_at_idx CC ISA i t \<longleftrightarrow>
   c \<in> reads_reg_caps CC (caps_of_regval ISA) (t ! i) \<and> i < length t"
  by (auto simp: reads_reg_caps_at_idx_def split: option.splits)

lemma member_reads_reg_caps_iff:
  "c \<in> reads_reg_caps CC c_of_r e \<longleftrightarrow>
   (\<exists>r v. e = E_read_reg r v \<and> c \<in> c_of_r v \<and> is_tagged_method CC c)"
  by (cases e) auto

lemma member_reads_reg_capsE[elim!]:
  assumes "c \<in> reads_reg_caps CC c_of_r e"
  obtains r v where "e = E_read_reg r v" and "c \<in> c_of_r v" and "is_tagged_method CC c"
  using assms
  by (auto simp: member_reads_reg_caps_iff)

lemma reads_reg_caps_Some_reads_mem_cap_None[simp]:
  assumes "c \<in> reads_reg_caps CC cor e"
  shows "reads_mem_cap CC e = None"
  using assms by (cases e) (auto simp: reads_mem_cap_def)

lemma writes_to_reg_at_idx_Some_iff[simp]:
  "writes_to_reg_at_idx i t = Some r \<longleftrightarrow> writes_to_reg (t ! i) = Some r \<and> i < length t"
  by (auto simp: writes_to_reg_at_idx_def bind_eq_Some_conv)

lemma writes_to_reg_SomeE[elim!]:
  assumes "writes_to_reg e = Some r"
  obtains v where "e = E_write_reg r v"
  using assms
  by (cases e) auto

lemma writes_to_reg_Some_iff:
  "writes_to_reg e = Some r \<longleftrightarrow> (\<exists>v. e = E_write_reg r v)"
  by (cases e) auto

lemma member_writes_reg_caps_at_idx_iff[simp]:
  "c \<in> writes_reg_caps_at_idx CC ISA i t \<longleftrightarrow>
   c \<in> writes_reg_caps CC (caps_of_regval ISA) (t ! i) \<and> i < length t"
  by (auto simp: writes_reg_caps_at_idx_def split: option.splits)

lemma member_writes_reg_capsE[elim!]:
  assumes "c \<in> writes_reg_caps CC c_of_r e"
  obtains r v where "e = E_write_reg r v" and "c \<in> c_of_r v" and "is_tagged_method CC c"
  using assms
  by (cases e) auto

lemma writes_mem_cap_at_idx_Some_iff[simp]:
  "writes_mem_cap_at_idx CC i t = Some (addr, sz, c) \<longleftrightarrow>
   writes_mem_cap CC (t ! i) = Some (addr, sz, c) \<and> i < length t"
  by (auto simp: writes_mem_cap_at_idx_def bind_eq_Some_conv)

lemma reads_mem_cap_at_idx_Some_iff[simp]:
  "reads_mem_cap_at_idx CC i t = Some (addr, sz, c) \<longleftrightarrow>
   reads_mem_cap CC (t ! i) = Some (addr, sz, c) \<and> i < length t"
  by (auto simp: reads_mem_cap_at_idx_def bind_eq_Some_conv)

lemma nth_append_left:
  assumes "i < length xs"
  shows "(xs @ ys) ! i = xs ! i"
  using assms by (auto simp: nth_append)

context Capability_ISA
begin

lemma writes_mem_cap_SomeE[elim!]:
  assumes "writes_mem_cap CC e = Some (addr, sz, c)"
  obtains wk bytes r where "e = E_write_memt wk addr sz bytes B1 r" and
    "cap_of_mem_bytes_method CC bytes B1 = Some c" and "is_tagged_method CC c"
  using assms
  by (cases e) (auto simp: writes_mem_cap_def bind_eq_Some_conv split: if_splits)

lemma writes_mem_cap_Some_iff:
  "writes_mem_cap CC e = Some (addr, sz, c) \<longleftrightarrow>
   (\<exists>wk bytes r. e = E_write_memt wk addr sz bytes B1 r \<and> cap_of_mem_bytes_method CC bytes B1 = Some c \<and> is_tagged_method CC c)"
  by (cases e) (auto simp: writes_mem_cap_def bind_eq_Some_conv)

lemma reads_mem_cap_SomeE[elim!]:
  assumes "reads_mem_cap CC e = Some (addr, sz, c)"
  obtains wk bytes r where "e = E_read_memt wk addr sz (bytes, B1)" and
    "cap_of_mem_bytes_method CC bytes B1 = Some c" and "is_tagged_method CC c"
  using assms
  by (cases e) (auto simp: reads_mem_cap_def bind_eq_Some_conv split: if_splits)

lemma reads_mem_cap_Some_iff:
  "reads_mem_cap CC e = Some (addr, sz, c) \<longleftrightarrow>
   (\<exists>wk bytes. e = E_read_memt wk addr sz (bytes, B1) \<and> cap_of_mem_bytes_method CC bytes B1 = Some c \<and> is_tagged_method CC c)"
  by (cases e; fastforce simp: reads_mem_cap_def bind_eq_Some_conv)

lemma available_reg_capsE:
  assumes "c \<in> available_reg_caps CC ISA i t"
  obtains r v j where "t ! j = E_read_reg r v"
    and "c \<in> caps_of_regval ISA v" and "is_tagged_method CC c"
    and "j < length t" and "j < i"
    and "r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<in> privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA j t"
  using assms
  by (induction i) (auto split: option.splits if_splits)

lemma available_mem_capsE:
  assumes "c \<in> available_mem_caps CC ISA i t"
  obtains wk paddr bytes j sz where "t ! j = E_read_memt wk paddr sz (bytes, B1)"
    and "\<not>is_translation_event ISA (t ! j)"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and "j < i" and "j < length t" and "is_tagged_method CC c"
  using assms
  by (induction i) (auto split: option.splits if_splits)

lemma available_caps_cases:
  assumes "c \<in> available_caps CC ISA use_mem_caps i t"
  obtains (Reg) r v j where "t ! j = E_read_reg r v"
    and "c \<in> caps_of_regval ISA v" and "is_tagged_method CC c"
    and "j < length t" and "j < i"
    and "r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<in> privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA j t"
  | (Mem) wk paddr bytes j sz where "t ! j = E_read_memt wk paddr sz (bytes, B1)"
    and "\<not>is_translation_event ISA (t ! j)"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and "j < i" and "j < length t" and "is_tagged_method CC c"
    and "use_mem_caps"
  using assms
  by (fastforce split: if_splits elim: available_reg_capsE available_mem_capsE)

lemma cap_reg_written_before_idx_0_False[simp]:
  "cap_reg_written_before_idx CC ISA 0 r t \<longleftrightarrow> False"
  by (auto simp: cap_reg_written_before_idx_def)

lemma cap_reg_written_before_idx_Suc_iff[simp]:
  "cap_reg_written_before_idx CC ISA (Suc i) r t \<longleftrightarrow>
   (cap_reg_written_before_idx CC ISA i r t \<or>
    (\<exists>v c. i < length t \<and> t ! i = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c))"
  by (fastforce simp: cap_reg_written_before_idx_def less_Suc_eq)

definition accessible_regs_at_idx :: "nat \<Rightarrow> 'regval trace \<Rightarrow> register_name set" where
  "accessible_regs_at_idx i t =
     {r. (r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA i r t) \<and>
         (r \<in> privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA i t)}"

fun accessed_reg_caps_of_ev :: "register_name set \<Rightarrow> 'regval event \<Rightarrow> 'cap set" where
  "accessed_reg_caps_of_ev regs (E_read_reg r v) =
     {c. r \<in> regs \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
| "accessed_reg_caps_of_ev regs _ = {}"

lemma member_accessed_reg_caps_of_evE[elim!]:
  assumes "c \<in> accessed_reg_caps_of_ev regs e"
  obtains r v where "e = E_read_reg r v" and "r \<in> regs"
    and "c \<in> caps_of_regval ISA v" and "is_tagged_method CC c"
  using assms
  by (cases e) auto

fun accessed_mem_caps_of_ev :: "'regval event \<Rightarrow> 'cap set" where
  "accessed_mem_caps_of_ev (E_read_memt rk a sz val) =
     (case cap_of_mem_bytes_method CC (fst val) (snd val) of
        Some c \<Rightarrow>
         if is_tagged_method CC c \<and> \<not>is_translation_event ISA (E_read_memt rk a sz val) then {c} else {}
      | None \<Rightarrow> {})"
| "accessed_mem_caps_of_ev _ = {}"

lemma member_accessed_mem_caps_of_evE[elim!]:
  assumes "c \<in> accessed_mem_caps_of_ev e"
  obtains rk a sz bytes tag where "e = E_read_memt rk a sz (bytes, tag)"
    and "cap_of_mem_bytes_method CC bytes tag = Some c" and "is_tagged_method CC c"
  using assms
  by (cases e) (auto split: option.splits if_splits)

fun allows_system_reg_access :: "register_name set \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "allows_system_reg_access accessible_regs (E_read_reg r v) =
     (\<exists>c \<in> caps_of_regval ISA v.
        is_tagged_method CC c \<and> \<not>is_sealed_method CC c \<and>
        permits_system_access_method CC c \<and>
        r \<in> PCC ISA \<inter> accessible_regs)"
| "allows_system_reg_access accessible_regs _ = False"

lemma system_access_permitted_before_idx_0[simp]:
  "system_access_permitted_before_idx CC ISA 0 t = False"
  by (auto simp: system_access_permitted_before_idx_def)

lemma system_access_permitted_before_idx_Suc[simp]:
  "system_access_permitted_before_idx CC ISA (Suc i) t \<longleftrightarrow>
     (system_access_permitted_before_idx CC ISA i t \<or>
      (i < length t \<and> allows_system_reg_access (accessible_regs_at_idx i t) (t ! i)))"
  by (fastforce simp: system_access_permitted_before_idx_def accessible_regs_at_idx_def less_Suc_eq
                elim!: allows_system_reg_access.elims)

lemma accessible_regs_at_idx_0[simp]:
  "accessible_regs_at_idx 0 t = (-privileged_regs ISA)"
  by (auto simp: accessible_regs_at_idx_def)

lemma accessible_regs_at_idx_Suc:
  "accessible_regs_at_idx (Suc i) t =
     (accessible_regs_at_idx i t \<union>
     (if i < length t \<and> allows_system_reg_access (accessible_regs_at_idx i t) (t ! i)
      then {r \<in> privileged_regs ISA. r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA i r t} else {})) -
     {r \<in> PCC ISA \<union> IDC ISA. \<exists>c v. i < length t \<and> t ! i = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
  by (auto simp: accessible_regs_at_idx_def)

lemma reads_from_reg_None_reads_reg_caps_empty[simp]:
  "reads_from_reg e = None \<Longrightarrow> reads_reg_caps CC cor e = {}"
  by (cases e) auto

declare available_reg_caps.simps[simp del]
declare available_mem_caps.simps[simp del]
declare available_caps.simps[simp del]

lemma available_reg_caps_0[simp]: "available_reg_caps CC ISA 0 t = {}"
  by (auto simp: available_reg_caps.simps)

lemma available_mem_caps_0[simp]: "available_mem_caps CC ISA 0 t = {}"
  by (auto simp: available_mem_caps.simps)

lemma available_caps_0[simp]: "available_caps CC ISA use_mem_caps 0 t = {}"
  by (auto simp: available_caps.simps)

lemma available_reg_caps_Suc:
  "available_reg_caps CC ISA (Suc i) t =
     available_reg_caps CC ISA i t
     \<union> (if i < length t then accessed_reg_caps_of_ev (accessible_regs_at_idx i t) (t ! i) else {})"
  by (cases "t ! i") (auto simp: available_reg_caps.simps accessible_regs_at_idx_def)

lemma available_mem_caps_Suc:
  "available_mem_caps CC ISA (Suc i) t =
     available_mem_caps CC ISA i t
     \<union> (if i < length t then accessed_mem_caps_of_ev (t ! i) else {})"
  by (cases "t ! i")
     (auto simp: available_mem_caps.simps reads_mem_cap_def bind_eq_Some_conv split: option.splits)

lemma available_caps_Suc:
  "available_caps CC ISA use_mem_caps (Suc i) t =
   available_caps CC ISA use_mem_caps i t \<union>
   (if i < length t then accessed_reg_caps_of_ev (accessible_regs_at_idx i t) (t ! i) else {}) \<union>
   (if i < length t \<and> use_mem_caps then accessed_mem_caps_of_ev (t ! i) else {})"
  by (auto simp: available_caps.simps available_reg_caps_Suc available_mem_caps_Suc)

abbreviation instr_sem_ISA ("\<lbrakk>_\<rbrakk>") where "\<lbrakk>instr\<rbrakk> \<equiv> instr_sem ISA instr"

end

lemma load_mem_axiomE:
  assumes "load_mem_axiom CC ISA is_fetch use_mem_caps invoked_indirect_caps t"
    and "reads_mem_val_at_idx i t = Some (paddr, sz, v, tag)"
    and "\<not>translation_event_at_idx ISA i t"
  obtains c' vaddr
  where "cap_derivable CC (available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) i t) c'"
    and "is_tagged_method CC c'"
    and "is_sealed_method CC c' \<longrightarrow> is_indirect_sentry_method CC c' \<and> unseal_method CC c' \<in> invoked_indirect_caps"
    and "translate_address ISA vaddr (if is_fetch then Fetch else Load) (take i t) = Some paddr"
    and "set (address_range vaddr sz) \<subseteq> get_mem_region CC c'"
    and "if is_fetch then permits_execute_method CC c' else permits_load_method CC c'"
    and "is_fetch \<longrightarrow> tag = B0"
    and "tag \<noteq> B0 \<and> use_mem_caps \<longrightarrow> permits_load_cap_method CC c' \<and> sz = tag_granule ISA \<and> address_tag_aligned ISA paddr"
  using assms
  unfolding load_mem_axiom_def
  by blast

lemma store_cap_reg_axiomE:
  assumes "store_cap_reg_axiom CC ISA has_ex use_mem_caps invoked_caps invoked_indirect_caps t"
    and "writes_to_reg_at_idx i t = Some r"
    and "c \<in> writes_reg_caps_at_idx CC ISA i t"
  obtains (Derivable) "cap_derivable CC (available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) i t) c"
  | (Ex) has_ex and "r \<in> PCC ISA"
    and "c \<in>  exception_targets ISA {v'. \<exists>r' j. j < i \<and> index t j = Some (E_read_reg r' v') \<and> r' \<in> KCC ISA}"
  | (Sentry) cs where "c \<in> invoked_caps"
    and "cap_derivable CC (available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) i t) cs"
    and "is_sentry_method CC cs" and "is_sealed_method CC cs"
    and "leq_cap CC c (unseal_method CC cs)" and "r \<in> PCC ISA"
  | (IndirectSentry) cs where "c \<in> invoked_indirect_caps"
    and "cap_derivable CC (available_reg_caps CC ISA i t) cs"
    and "is_indirect_sentry_method CC cs" and "is_sealed_method CC cs"
    and "leq_cap CC c (unseal_method CC cs)" and "r \<in> IDC ISA"
  | (CCall) cc cd where "c \<in> invoked_caps"
    and "cap_derivable CC (available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) i t) cc"
    and "cap_derivable CC (available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) i t) cd"
    and "invokable CC cc cd"
    and "(leq_cap CC c (unseal_method CC cc) \<and> r \<in> PCC ISA) \<or> (leq_cap CC c (unseal_method CC cd) \<and> r \<in> IDC ISA)"
  | (Indirect) c' where "c \<in> invoked_caps"
    and "cap_derivable CC (available_mem_caps CC ISA i t) c'"
    and "(leq_cap CC c (unseal_method CC c') \<and> is_sealed_method CC c' \<and> is_sentry_method CC c' \<and> r \<in> PCC ISA) \<or>
         (leq_cap CC c c' \<and> r \<in> PCC ISA \<union> IDC ISA)"
  using assms
  unfolding store_cap_reg_axiom_def
  by (elim allE[where x = i] allE[where x = c] allE[where x = r]) blast

(*lemma store_cap_reg_axiom_invoked_caps_mono:
  fixes invoked_caps :: "('cap \<times> 'cap) set"
  assumes "store_cap_reg_axiom CC ISA has_ex invoked_caps t"
    and "invoked_caps \<subseteq> invoked_caps'"
  shows "store_cap_reg_axiom CC ISA has_ex invoked_caps' t"
  using assms
  unfolding store_cap_reg_axiom_def
  by blast*)

end
