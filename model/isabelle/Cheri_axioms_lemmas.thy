theory Cheri_axioms_lemmas
imports Capabilities_lemmas Cheri_axioms
begin

locale Capability_ISA = Capabilities CC
  for CC :: "'cap Capability_class" +
  fixes ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and initial_caps :: "'cap set"

abbreviation "instr_trace instr t \<equiv> \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
abbreviation "fetch_trace t \<equiv> \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"

lemma trace_invokes_simps[simp]:
  "trace_invokes_code_caps ISA (instr_trace instr t) = instr_invokes_code_caps ISA instr t"
  "trace_invokes_code_caps ISA (fetch_trace t) = {}"
  "trace_invokes_data_caps ISA (instr_trace instr t) = instr_invokes_data_caps ISA instr t"
  "trace_invokes_data_caps ISA (fetch_trace t) = {}"
  "trace_invokes_indirect_caps ISA (instr_trace instr t) = instr_invokes_indirect_caps ISA instr t"
  "trace_invokes_indirect_caps ISA (fetch_trace t) = {}"
  by (auto simp: trace_invokes_code_caps_def trace_invokes_data_caps_def trace_invokes_indirect_caps_def)

declare event_at_idx_def[simp]

lemma reads_from_reg_at_idx_Some_iff[simp]:
  "reads_from_reg_at_idx i t = Some r \<longleftrightarrow> reads_from_reg (trace t ! i) = Some r \<and> i < length (trace t)"
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
   c \<in> reads_reg_caps CC (caps_of_regval ISA) (trace t ! i) \<and> i < length (trace t)"
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
  "writes_to_reg_at_idx i t = Some r \<longleftrightarrow> writes_to_reg (trace t ! i) = Some r \<and> i < length (trace t)"
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
   c \<in> writes_reg_caps CC (caps_of_regval ISA) (trace t ! i) \<and> i < length (trace t)"
  by (auto simp: writes_reg_caps_at_idx_def split: option.splits)

lemma member_writes_reg_capsE[elim!]:
  assumes "c \<in> writes_reg_caps CC c_of_r e"
  obtains r v where "e = E_write_reg r v" and "c \<in> c_of_r v" and "is_tagged_method CC c"
  using assms
  by (cases e) auto

lemma member_writes_reg_caps_iff:
  "c \<in> writes_reg_caps CC c_of_v e \<longleftrightarrow>
   (\<exists>r v. e = E_write_reg r v \<and> c \<in> c_of_v v \<and> is_tagged_method CC c)"
  by (cases e) auto

lemma writes_mem_cap_at_idx_Some_iff[simp]:
  "writes_mem_cap_at_idx CC i t = Some (addr, sz, c) \<longleftrightarrow>
   writes_mem_cap CC (trace t ! i) = Some (addr, sz, c) \<and> i < length (trace t)"
  by (auto simp: writes_mem_cap_at_idx_def bind_eq_Some_conv)

lemma reads_mem_cap_at_idx_Some_iff[simp]:
  "reads_mem_cap_at_idx CC i t = Some (addr, sz, c) \<longleftrightarrow>
   reads_mem_cap CC (trace t ! i) = Some (addr, sz, c) \<and> i < length (trace t)"
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
  obtains r v j where "trace t ! j = E_read_reg r v"
    and "c \<in> caps_of_regval ISA v" and "is_tagged_method CC c"
    and "j < length (trace t)" and "j < i"
    and "r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<in> read_privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA j t"
  using assms
  by (induction i) (auto split: option.splits if_splits)

lemma accessed_mem_caps_at_idxE:
  assumes "(paddr, c) \<in> accessed_mem_caps_at_idx CC ISA i t"
  obtains wk bytes j sz where "trace t ! j = E_read_memt wk paddr sz (bytes, B1)"
    and "\<not>is_translation_event ISA (trace t ! j)"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and "j < i" and "j < length (trace t)" and "is_tagged_method CC c"
  using assms
  by (induction i) (auto split: option.splits if_splits)

lemma available_mem_caps_accessed_mem_caps_at_idx:
  "available_mem_caps CC ISA i t = snd ` accessed_mem_caps_at_idx CC ISA i t"
  by (fastforce simp: available_mem_caps_def image_iff eq_snd_iff)

lemma available_mem_capsE:
  assumes "c \<in> available_mem_caps CC ISA i t"
  obtains wk paddr bytes j sz where "trace t ! j = E_read_memt wk paddr sz (bytes, B1)"
    and "\<not>is_translation_event ISA (trace t ! j)"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and "j < i" and "j < length (trace t)" and "is_tagged_method CC c"
  using assms[unfolded available_mem_caps_def]
  by (auto elim: accessed_mem_caps_at_idxE)

lemma available_caps_cases:
  assumes "c \<in> available_caps CC ISA i t"
  obtains (Reg) r v j where "trace t ! j = E_read_reg r v"
    and "c \<in> caps_of_regval ISA v" and "is_tagged_method CC c"
    and "j < length (trace t)" and "j < i"
    and "r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<in> read_privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA j t"
  | (Mem) wk paddr bytes j sz where "trace t ! j = E_read_memt wk paddr sz (bytes, B1)"
    and "\<not>is_translation_event ISA (trace t ! j)"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and "j < i" and "j < length (trace t)" and "is_tagged_method CC c"
    and "trace_uses_mem_caps ISA t" and "trace_invokes_indirect_caps ISA t = {}"
  using assms
  unfolding available_caps_def
  by (fastforce split: if_splits elim: available_reg_capsE available_mem_capsE)

lemma cap_reg_written_before_idx_0_False[simp]:
  "cap_reg_written_before_idx CC ISA 0 r t \<longleftrightarrow> False"
  by (auto simp: cap_reg_written_before_idx_def)

lemma cap_reg_written_before_idx_Suc_iff[simp]:
  "cap_reg_written_before_idx CC ISA (Suc i) r t \<longleftrightarrow>
   (cap_reg_written_before_idx CC ISA i r t \<or>
    (\<exists>v c. i < length (trace t) \<and> trace t ! i = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c))"
  by (fastforce simp: cap_reg_written_before_idx_def less_Suc_eq)

definition accessible_regs_at_idx :: "nat \<Rightarrow> ('regval, 'instr) isa_trace \<Rightarrow> register_name set" where
  "accessible_regs_at_idx i t =
     {r. (r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA i r t) \<and>
         (r \<in> read_privileged_regs ISA \<longrightarrow> system_access_permitted_before_idx CC ISA i t)}"

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

fun mem_cap_loads_of_ev :: "'regval event \<Rightarrow> (nat * 'cap) set" where
  "mem_cap_loads_of_ev (E_read_memt rk addr sz val) =
     (case cap_of_mem_bytes_method CC (fst val) (snd val) of
        Some c \<Rightarrow>
         if is_tagged_method CC c \<and> \<not>is_translation_event ISA (E_read_memt rk addr sz val) then {(addr, c)} else {}
      | None \<Rightarrow> {})"
| "mem_cap_loads_of_ev _ = {}"

fun accessed_mem_caps_of_ev :: "'regval event \<Rightarrow> 'cap set" where
  "accessed_mem_caps_of_ev (E_read_memt rk a sz val) =
     (case cap_of_mem_bytes_method CC (fst val) (snd val) of
        Some c \<Rightarrow>
         if is_tagged_method CC c \<and> \<not>is_translation_event ISA (E_read_memt rk a sz val) then {c} else {}
      | None \<Rightarrow> {})"
| "accessed_mem_caps_of_ev _ = {}"

lemma accessed_mem_caps_snd_mem_cap_loads_of_ev:
  "accessed_mem_caps_of_ev e = snd ` mem_cap_loads_of_ev e"
  by (cases e; auto split: option.splits)

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
      (i < length (trace t) \<and> allows_system_reg_access (accessible_regs_at_idx i t) (trace t ! i)))"
  by (fastforce simp: system_access_permitted_before_idx_def accessible_regs_at_idx_def less_Suc_eq
                elim!: allows_system_reg_access.elims)

lemma accessible_regs_at_idx_0[simp]:
  "accessible_regs_at_idx 0 t = (-read_privileged_regs ISA)"
  by (auto simp: accessible_regs_at_idx_def)

lemma accessible_regs_at_idx_Suc:
  "accessible_regs_at_idx (Suc i) t =
     (accessible_regs_at_idx i t \<union>
     (if i < length (trace t) \<and> allows_system_reg_access (accessible_regs_at_idx i t) (trace t ! i)
      then {r \<in> read_privileged_regs ISA. r \<in> PCC ISA \<or> r \<in> IDC ISA \<longrightarrow> \<not>cap_reg_written_before_idx CC ISA i r t} else {})) -
     {r \<in> PCC ISA \<union> IDC ISA. \<exists>c v. i < length (trace t) \<and> trace t ! i = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
  by (auto simp: accessible_regs_at_idx_def)

lemma reads_from_reg_None_reads_reg_caps_empty[simp]:
  "reads_from_reg e = None \<Longrightarrow> reads_reg_caps CC cor e = {}"
  by (cases e) auto

declare available_reg_caps.simps[simp del]
declare accessed_mem_caps_at_idx.simps[simp del]

lemma available_reg_caps_0[simp]: "available_reg_caps CC ISA 0 t = {}"
  by (auto simp: available_reg_caps.simps)

lemma accessed_mem_caps_at_idx_0[simp]: "accessed_mem_caps_at_idx CC ISA 0 t = {}"
  by (auto simp: accessed_mem_caps_at_idx.simps)

lemma available_mem_caps_0[simp]: "available_mem_caps CC ISA 0 t = {}"
  by (auto simp: available_mem_caps_accessed_mem_caps_at_idx)

lemma available_caps_0[simp]: "available_caps CC ISA 0 t = {}"
  by (auto simp: available_caps_def)

lemma available_reg_caps_Suc:
  "available_reg_caps CC ISA (Suc i) t =
     available_reg_caps CC ISA i t
     \<union> (if i < length (trace t) then accessed_reg_caps_of_ev (accessible_regs_at_idx i t) (trace t ! i) else {})"
  by (cases "trace t ! i") (auto simp: available_reg_caps.simps accessible_regs_at_idx_def)

lemma accessed_mem_caps_at_idx_Suc:
  "accessed_mem_caps_at_idx CC ISA (Suc i) t =
     accessed_mem_caps_at_idx CC ISA i t
     \<union> (if i < length (trace t) then mem_cap_loads_of_ev (trace t ! i) else {})"
  by (cases "trace t ! i")
     (auto simp: accessed_mem_caps_at_idx.simps reads_mem_cap_def bind_eq_Some_conv split: option.splits)

lemma available_mem_caps_Suc:
  "available_mem_caps CC ISA (Suc i) t =
     available_mem_caps CC ISA i t
     \<union> (if i < length (trace t) then accessed_mem_caps_of_ev (trace t ! i) else {})"
  unfolding available_mem_caps_accessed_mem_caps_at_idx accessed_mem_caps_at_idx_Suc
  by (auto simp:  accessed_mem_caps_snd_mem_cap_loads_of_ev)

lemma available_caps_Suc:
  "available_caps CC ISA (Suc i) t =
   available_caps CC ISA i t \<union>
   (if i < length (trace t) then accessed_reg_caps_of_ev (accessible_regs_at_idx i t) (trace t ! i) else {}) \<union>
   (if i < length (trace t) \<and> trace_uses_mem_caps ISA t \<and> trace_invokes_indirect_caps ISA t = {} then accessed_mem_caps_of_ev (trace t ! i) else {})"
  by (auto simp: available_caps_def available_reg_caps_Suc available_mem_caps_Suc)

abbreviation "instr_cheri_axioms instr t n \<equiv> cheri_axioms CC ISA initial_caps n (instr_trace instr t)"

abbreviation "fetch_cheri_axioms t n \<equiv> cheri_axioms CC ISA initial_caps n (fetch_trace t)"

lemma writes_mem_val_at_idx_eq_Some_iff[simp]:
  "writes_mem_val_at_idx i t = Some (addr, sz, v, tag) \<longleftrightarrow>
   i < length (trace t) \<and> writes_mem_val (trace t ! i) = Some (addr, sz, v, tag)"
  by (auto simp: writes_mem_val_at_idx_def bind_eq_Some_conv)

abbreviation instr_sem_ISA ("\<lbrakk>_\<rbrakk>") where "\<lbrakk>instr\<rbrakk> \<equiv> instr_sem ISA instr"

end

lemma load_mem_axiomE:
  assumes "load_mem_axiom CC ISA initial_caps n t"
    and "reads_mem_val_at_idx i t = Some (paddr, sz, v, tag)"
    and "\<not>translation_event_at_idx ISA i t"
    and "i < n"
  obtains c' vaddr
  where "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c'"
    and "is_tagged_method CC c'"
    and "is_sealed_method CC c' \<longrightarrow> is_indirect_sentry CC c' \<and> unseal_method CC c' \<in> trace_invokes_indirect_caps ISA t"
    and "translate_address ISA vaddr (if is_fetch_trace t then Fetch else Load) (take i (trace t)) = Some paddr"
    and "set (address_range vaddr sz) \<subseteq> get_mem_region CC c'"
    and "if is_fetch_trace t then permits_execute_method CC c' else permits_load_method CC c'"
    and "is_fetch_trace t \<longrightarrow> tag = B0"
    and "tag \<noteq> B0 \<and> trace_uses_mem_caps ISA t \<longrightarrow> permits_load_cap_method CC c' \<and> sz = tag_granule ISA \<and> address_tag_aligned ISA paddr"
  using assms
  unfolding load_mem_axiom_def
  by blast

lemma store_cap_reg_axiomE:
  assumes "store_cap_reg_axiom CC ISA initial_caps n t"
    and "writes_to_reg_at_idx i t = Some r"
    and "c \<in> writes_reg_caps_at_idx CC ISA i t"
    and "i < n"
  obtains (Derivable) "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c"
  | (Ex) "trace_raises_ex ISA t" and "r \<in> PCC ISA"
    and "c \<in>  exception_targets_at_idx ISA i t"
  | (Invoked_Code_Cap) "is_invoked_code_cap_at_idx CC ISA c t i" and "r \<in> PCC ISA"
  | (Invoked_Data_Cap) "is_invoked_data_cap_at_idx CC ISA c t i" and "r \<in> IDC ISA"
  using assms
  unfolding store_cap_reg_axiom_def
  by blast

locale Capability_ISA_Fixed_Translation = Capability_ISA CC ISA initial_caps
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and initial_caps :: "'cap set" +
  fixes translation_assms :: "'regval event \<Rightarrow> bool"
  assumes fixed_translation: "\<And>i t addr load. \<forall>e \<in> set t. translation_assms e \<Longrightarrow> translate_address ISA addr load (take i t) = translate_address ISA addr load []"
begin

abbreviation "translation_assms_trace t \<equiv> \<forall>e \<in> set t. translation_assms e"

end

locale Capability_Invariant_ISA = Capability_ISA CC ISA initial_caps + Capabilities_Invariant CC cap_invariant
  for CC :: "'cap Capability_class"
  and ISA :: "('cap, 'regval, 'instr, 'e) isa"
  and initial_caps :: "'cap set"
  and cap_invariant :: "'cap \<Rightarrow> bool"
begin

fun cap_inv_ev :: "'regval event \<Rightarrow> bool" where
  "cap_inv_ev (E_read_reg r v) =
     (\<forall>c \<in> caps_of_regval ISA v. is_tagged_method CC c \<longrightarrow> cap_invariant c)"
| "cap_inv_ev (E_read_memt rk addr sz (v, t)) =
     (case cap_of_mem_bytes_method CC v t of
        Some c \<Rightarrow> (is_tagged_method CC c \<longrightarrow> cap_invariant c)
      | None \<Rightarrow> True)"
| "cap_inv_ev _ = True"

abbreviation "cap_inv_trace t \<equiv> (\<forall>e \<in> set t. cap_inv_ev e)"

definition available_caps_invariant :: "('regval, 'instr) isa_trace \<Rightarrow> nat \<Rightarrow> bool" where
  "available_caps_invariant t n \<equiv>
   (\<forall>i < n. \<forall>c \<in> initial_caps \<union> available_caps CC ISA i t.
      is_tagged_method CC c \<longrightarrow> cap_invariant c)"

(*abbreviation
  "instr_available_caps instr n t \<equiv>
   available_caps CC ISA (invokes_indirect_caps ISA instr t = {} \<and> uses_mem_caps ISA instr t) n t"*)

abbreviation
  "instr_available_caps_invariant instr t n \<equiv>
   available_caps_invariant (instr_trace instr t) n"

abbreviation "fetch_available_caps_invariant t n \<equiv> available_caps_invariant (fetch_trace t) n"

end

end
