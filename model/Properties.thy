theory Properties
imports Cheri_axioms_lemmas Sail.Sail2_state_lemmas
begin

section \<open>Helper lemmas and definitions\<close>

text \<open>TODO: Add to the Sail library\<close>

lemma Traces_runTrace[simp]:
  "(m, t, m') \<in> Traces \<Longrightarrow> runTrace t m = Some m'"
  by (auto simp: runTrace_iff_Traces)

fun consumesTrace :: "('regval, 'a, 'e) monad \<Rightarrow> 'regval trace \<Rightarrow> nat option" where
  "consumesTrace m [] = (if final m then Some 0 else None)"
| "consumesTrace m (e # t) =
     (if final m then Some 0 else
      case emitEvent m e of
        Some m' \<Rightarrow> (case consumesTrace m' t of Some n \<Rightarrow> Some (Suc n) | None \<Rightarrow> None)
      | None \<Rightarrow> None)"

lemma hasTrace_iff_runTrace_final:
  "hasTrace t m \<longleftrightarrow> (\<exists>m'. runTrace t m = Some m' \<and> final m')"
  by (auto simp: hasTrace_def split: option.splits)

lemma hasTrace_Cons_emitEvent:
  "hasTrace (e # t) m \<longleftrightarrow> (\<exists>m'. emitEvent m e = Some m' \<and> hasTrace t m')"
  by (cases "emitEvent m e") (auto simp: hasTrace_def)

lemma final_emitEvent_None:
  assumes "final m"
  shows "emitEvent m e = None"
  using assms
  by (cases rule: final_cases) (auto simp: emitEvent_def split: event.splits)

lemma final_runTrace_Nil:
  assumes "final m"
  shows "runTrace t m = Some m' \<longleftrightarrow> t = [] \<and> m' = m"
  using assms
  by (cases t) (auto simp: final_emitEvent_None)

lemma final_hasTrace_Nil:
  "final m \<Longrightarrow> hasTrace t m \<longleftrightarrow> t = []"
  by (auto simp: hasTrace_def final_runTrace_Nil split: option.splits)

lemma final_consumesTrace_Nil:
  "final m \<Longrightarrow> consumesTrace m t = Some 0"
  by (cases t) auto

lemma hasTrace_consumesTrace:
  assumes "hasTrace t m"
  shows "consumesTrace m (t @ t') = Some (length t)"
  using assms
  by (induction t m rule: runTrace.induct)
     (auto simp: hasTrace_iff_runTrace_final final_emitEvent_None final_consumesTrace_Nil
           simp: bind_eq_Some_conv split: option.splits)

lemma hasTrace_take_consumesTrace:
  assumes "hasTrace (take n t) m" and "n \<le> length t"
  shows "consumesTrace m t = Some n"
  using assms hasTrace_consumesTrace[where t = "take n t" and t' = "drop n t"]
  by (auto simp: min_absorb2)

lemma consumesTrace_hasTrace:
  assumes "consumesTrace m t = Some n"
  shows "hasTrace (take n t) m"
  using assms
  by (induction m t arbitrary: n rule: consumesTrace.induct)
     (auto simp: final_hasTrace_Nil hasTrace_Cons_emitEvent split: if_splits option.splits)

lemma consumesTrace_length:
  assumes "consumesTrace m t = Some n"
  shows "n \<le> length t"
  using assms
  by (induction m t arbitrary: n rule: consumesTrace.induct) (auto split: if_splits option.splits)

lemma consumesTrace_iff_hasTrace:
  "consumesTrace m t = Some n \<longleftrightarrow> hasTrace (take n t) m \<and> n \<le> length t"
  by (auto intro: hasTrace_take_consumesTrace consumesTrace_hasTrace consumesTrace_length)

lemma runTraceS_rev_induct[consumes 1, case_names Init Step]:
  assumes "runTraceS ra t s = Some s'"
    and Init: "P [] s"
    and Step: "\<And>t e s'' s'. runTraceS ra t s = Some s'' \<Longrightarrow> emitEventS ra e s'' = Some s' \<Longrightarrow> P t s'' \<Longrightarrow> P (t @ [e]) s'"
  shows "P t s'"
  using assms
  by (induction t arbitrary: s' rule: rev_induct)
     (auto elim: runTraceS_appendE runTraceS_ConsE simp: bind_eq_Some_conv)

lemma runTraceS_appendI:
  assumes "runTraceS ra t s = Some s''" and "runTraceS ra t' s'' = Some s'"
  shows "runTraceS ra (t @ t') s = Some s'"
  using assms
  by (induction t arbitrary: s) (auto simp: bind_eq_Some_conv)

lemma runTraceS_append_iff:
  "runTraceS ra (t @ t') s = Some s' \<longleftrightarrow> (\<exists>s''. runTraceS ra t s = Some s'' \<and> runTraceS ra t' s'' = Some s')"
  by (auto intro: runTraceS_appendI elim: runTraceS_appendE)

lemma Run_hasTrace: "Run m t a \<Longrightarrow> hasTrace t m"
  by (auto simp: hasTrace_iff_Traces_final final_def)

section \<open>Single-instruction monotonicity\<close>

locale CHERI_ISA = Capability_Invariant_ISA CC ISA initial_caps cap_invariant
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and cap_invariant :: "'cap \<Rightarrow> bool" and initial_caps :: "'cap set" +
  fixes fetch_assms :: "'regval trace \<Rightarrow> bool" and instr_assms :: "'instr \<Rightarrow> 'regval trace \<Rightarrow> bool"
  assumes instr_cheri_axioms: "\<And>t n instr. hasTrace t \<lbrakk>instr\<rbrakk> \<Longrightarrow> n \<le> length t \<Longrightarrow> instr_available_caps_invariant instr t n \<Longrightarrow> instr_assms instr t \<Longrightarrow> instr_cheri_axioms instr t n"
    and fetch_cheri_axioms: "\<And>t n. hasTrace t (instr_fetch ISA) \<Longrightarrow> n \<le> length t \<Longrightarrow> fetch_available_caps_invariant t n \<Longrightarrow> fetch_assms t \<Longrightarrow> fetch_cheri_axioms t n"

locale Register_Accessors =
  fixes read_regval :: "register_name \<Rightarrow> 'regs \<Rightarrow> 'regval option"
    and write_regval :: "register_name \<Rightarrow> 'regval \<Rightarrow> 'regs \<Rightarrow> 'regs option"
begin

abbreviation "s_emit_event e s \<equiv> emitEventS (read_regval, write_regval) e s"
abbreviation "s_run_trace t s \<equiv> runTraceS (read_regval, write_regval) t s"
abbreviation "s_allows_trace t s \<equiv> \<exists>s'. s_run_trace t s = Some s'"

end

locale CHERI_ISA_State =
  CHERI_ISA CC ISA cap_invariant initial_caps fetch_assms instr_assms +
  Register_Accessors read_regval write_regval
  for CC :: "'cap Capability_class"
  and ISA :: "('cap, 'regval, 'instr, 'e) isa"
  and cap_invariant :: "'cap \<Rightarrow> bool"
  and initial_caps :: "'cap set"
  and fetch_assms :: "'regval trace \<Rightarrow> bool"
  and instr_assms :: "'instr \<Rightarrow> 'regval trace \<Rightarrow> bool"
  and read_regval :: "register_name \<Rightarrow> 'regs \<Rightarrow> 'regval option"
  and write_regval :: "register_name \<Rightarrow> 'regval \<Rightarrow> 'regs \<Rightarrow> 'regs option" +
  (* State versions of ISA model parameters *)
  fixes s_translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> 'regs sequential_state \<Rightarrow> nat option"
  (* TODO: Add optional register_value state generation to Sail where the next two hold by construction *)
  assumes read_absorb_write: "\<And>r v s s'. write_regval r v s = Some s' \<Longrightarrow> read_regval r s' = Some v"
    and read_ignore_write: "\<And>r r' v s s'. write_regval r v s = Some s' \<Longrightarrow> r' \<noteq> r \<Longrightarrow> read_regval r' s' = read_regval r' s"
    and translate_address_sound: "\<And>t s vaddr paddr load.
          s_allows_trace t s \<Longrightarrow>
          translate_address ISA vaddr load t = Some paddr \<Longrightarrow>
          s_translate_address vaddr load s = Some paddr"
    and translate_address_tag_aligned_iff: "\<And>s vaddr paddr load.
          s_translate_address vaddr load s = Some paddr \<Longrightarrow>
          address_tag_aligned ISA paddr \<longleftrightarrow> address_tag_aligned ISA vaddr"
begin

fun get_reg_val :: "register_name \<Rightarrow> 'regs sequential_state \<Rightarrow> 'regval option" where
  "get_reg_val r s = read_regval r (regstate s)"

fun put_reg_val :: "register_name \<Rightarrow> 'regval \<Rightarrow> 'regs sequential_state \<Rightarrow> 'regs sequential_state option" where
  "put_reg_val r v s = map_option (\<lambda>rs'. s\<lparr>regstate := rs'\<rparr>) (write_regval r v (regstate s))"

fun get_reg_caps :: "register_name \<Rightarrow> 'regs sequential_state \<Rightarrow> 'cap set" where
  "get_reg_caps r s = (case read_regval r (regstate s) of Some v \<Rightarrow> {c \<in> caps_of_regval ISA v. is_tagged_method CC c} | None \<Rightarrow> {})"

fun get_mem_cap :: "nat \<Rightarrow> nat \<Rightarrow> 'regs sequential_state \<Rightarrow> 'cap option" where
  "get_mem_cap addr sz s =
     Option.bind (get_mem_bytes addr sz s) (\<lambda>(bytes, tag).
     Option.bind (cap_of_mem_bytes_method CC bytes tag) (\<lambda>c.
     if is_tagged_method CC c then Some c else None))"

fun get_aligned_mem_cap :: "nat \<Rightarrow> nat \<Rightarrow> 'regs sequential_state \<Rightarrow> 'cap option" where
  "get_aligned_mem_cap vaddr sz s =
     (if address_tag_aligned ISA vaddr \<and> sz = tag_granule ISA then get_mem_cap vaddr sz s else None)"

fun s_invariant :: "('regs sequential_state \<Rightarrow> 'a) \<Rightarrow> 'regval trace \<Rightarrow> 'regs sequential_state \<Rightarrow> bool" where
  "s_invariant f [] s = True"
| "s_invariant f (e # t) s = (case s_emit_event e s of Some s' \<Rightarrow> f s' = f s \<and> s_invariant f t s' | None \<Rightarrow> False)"

abbreviation s_invariant_holds :: "('regs sequential_state \<Rightarrow> bool) \<Rightarrow> 'regval trace \<Rightarrow> 'regs sequential_state \<Rightarrow> bool" where
  "s_invariant_holds P t s \<equiv> P s \<and> s_invariant P t s"

lemma s_invariant_append:
  "s_invariant f (\<beta> @ \<alpha>) s \<longleftrightarrow>
   (\<exists>s'. s_invariant f \<beta> s \<and> s_run_trace \<beta> s = Some s' \<and> s_invariant f \<alpha> s')"
  by (induction \<beta> arbitrary: s) (auto split: option.splits simp: runTraceS_Cons_tl)

lemma s_invariant_takeI:
  assumes "s_invariant f t s"
  shows "s_invariant f (take n t) s"
proof -
  from assms have "s_invariant f (take n t @ drop n t) s" by auto
  then show ?thesis unfolding s_invariant_append by auto
qed

lemma s_invariant_run_trace_eq:
  assumes "s_invariant f t s" and "s_run_trace t s = Some s'"
  shows "f s' = f s"
  using assms
  by (induction f t s rule: s_invariant.induct)
     (auto split: option.splits elim: runTraceS_ConsE)

lemma s_invariant_holds_weaken:
  assumes "s_invariant_holds P t s"
    and "\<And>s'. P s \<Longrightarrow> P s' \<Longrightarrow> Q s'"
  shows "s_invariant_holds Q t s"
  using assms
  by (induction P t s rule: s_invariant.induct) (auto split: option.split_asm)

lemma take_s_invariantI:
  assumes "s_run_trace t s = Some s'"
    and inv: "\<And>n s''. s_run_trace (take n t) s = Some s'' \<Longrightarrow> n \<le> length t \<Longrightarrow> f s'' = f s"
  shows "s_invariant f t s"
proof (use assms in \<open>induction t s' rule: runTraceS_rev_induct\<close>)
  case Init
  then show ?case by auto
next
  case (Step t e s'' s')
  moreover have "f s'' = f s" and "f s' = f s"
    using Step.hyps Step.prems[of "length t"] Step.prems[of "Suc (length t)"]
    by (auto simp: runTraceS_append_iff)
  moreover have "s_invariant f t s"
  proof (rule Step.IH)
    fix n s''
    assume "s_run_trace (take n t) s = Some s''" and "n \<le> length t"
    then show "f s'' = f s"
      by (intro Step.prems[of n]) auto
  qed
  ultimately show ?case
    by (auto simp: s_invariant_append)
qed

lemma take_s_invariant_holdsI[consumes 1, case_names Init Inv]:
  assumes t: "s_run_trace t s = Some s'"
    and init: "P s"
    and inv: "\<And>n s''. s_run_trace (take n t) s = Some s'' \<Longrightarrow> n \<le> length t \<Longrightarrow> P s''"
  shows "s_invariant_holds P t s"
  using assms
  by (auto intro: take_s_invariantI)

inductive_set reachable_caps :: "'regs sequential_state \<Rightarrow> 'cap set" for s :: "'regs sequential_state" where
  Reg: "\<lbrakk>c \<in> get_reg_caps r s; r \<notin> read_privileged_regs ISA; is_tagged_method CC c\<rbrakk> \<Longrightarrow> c \<in> reachable_caps s"
| SysReg:
    "\<lbrakk>c \<in> get_reg_caps r s; r \<in> read_privileged_regs ISA;
      c' \<in> reachable_caps s; permits_system_access_method CC c'; is_tagged_method CC c'; \<not>is_sealed_method CC c';
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps s"
| Mem:
    "\<lbrakk>get_aligned_mem_cap addr (tag_granule ISA) s = Some c;
      s_translate_address vaddr Load s = Some addr;
      c' \<in> reachable_caps s; is_tagged_method CC c'; \<not>is_sealed_method CC c';
      set (address_range vaddr (tag_granule ISA)) \<subseteq> get_mem_region CC c';
      permits_load_cap_method CC c';
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps s"
| Restrict: "\<lbrakk>c \<in> reachable_caps s; leq_cap CC c' c\<rbrakk> \<Longrightarrow> c' \<in> reachable_caps s"
| Seal:
    "\<lbrakk>c' \<in> reachable_caps s; c'' \<in> reachable_caps s; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; \<not>is_sealed_method CC c'; permits_seal_method CC c'';
      get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     seal_method CC c' (get_cursor_method CC c'') \<in> reachable_caps s"
| SealEntry:
    "\<lbrakk>c' \<in> reachable_caps s; \<not>is_sealed_method CC c';
      is_sentry_method CC (seal_method CC c' otype) \<or> is_indirect_sentry_method CC (seal_method CC c' otype)\<rbrakk> \<Longrightarrow>
     seal_method CC c' otype \<in> reachable_caps s"
| Unseal:
    "\<lbrakk>c' \<in> reachable_caps s; c'' \<in> reachable_caps s; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; is_sealed_method CC c'; permits_unseal_method CC c'';
      get_obj_type_method CC c' = get_cursor_method CC c'';
      get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     clear_global_unless CC (is_global_method CC c'') (unseal_method CC c') \<in> reachable_caps s"

lemma derivable_subseteq_reachableI:
  assumes "C \<subseteq> reachable_caps s"
  shows "derivable C \<subseteq> reachable_caps s"
proof
  fix c
  assume "c \<in> derivable C"
  then show "c \<in> reachable_caps s" using assms
    by induction (auto intro: reachable_caps.intros)
qed

lemma derivable_subseteq_reachableE:
  assumes "derivable C \<subseteq> reachable_caps s"
  shows "C \<subseteq> reachable_caps s"
  using assms by (auto intro: derivable.intros)

lemma derivable_reachable_caps_idem: "derivable (reachable_caps s) = reachable_caps s"
  using derivable_subseteq_reachableI[of "reachable_caps s" s] derivable_refl
  by auto

inductive_set reachable_caps_plus :: "'cap set \<Rightarrow> 'regs sequential_state \<Rightarrow> 'cap set"
  for C :: "'cap set" and s :: "'regs sequential_state"
where
  Reg: "\<lbrakk>c \<in> get_reg_caps r s; r \<notin> read_privileged_regs ISA; is_tagged_method CC c\<rbrakk> \<Longrightarrow> c \<in> reachable_caps_plus C s"
| SysReg:
    "\<lbrakk>c \<in> get_reg_caps r s; r \<in> read_privileged_regs ISA;
      c' \<in> reachable_caps_plus C s; permits_system_access_method CC c'; is_tagged_method CC c'; \<not>is_sealed_method CC c';
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps_plus C s"
| Mem:
    "\<lbrakk>get_aligned_mem_cap addr (tag_granule ISA) s = Some c;
      s_translate_address vaddr Load s = Some addr;
      c' \<in> reachable_caps_plus C s; is_tagged_method CC c'; \<not>is_sealed_method CC c';
      set (address_range vaddr (tag_granule ISA)) \<subseteq> get_mem_region CC c';
      permits_load_cap_method CC c';
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps_plus C s"
| Plus: "c \<in> C \<Longrightarrow> c \<in> reachable_caps_plus C s"
| Restrict: "\<lbrakk>c \<in> reachable_caps_plus C s; leq_cap CC c' c\<rbrakk> \<Longrightarrow> c' \<in> reachable_caps_plus C s"
| Seal:
    "\<lbrakk>c' \<in> reachable_caps_plus C s; c'' \<in> reachable_caps_plus C s;
      is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; \<not>is_sealed_method CC c'; permits_seal_method CC c'';
      get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     seal_method CC c' (get_cursor_method CC c'') \<in> reachable_caps_plus C s"
| SealEntry:
    "\<lbrakk>c' \<in> reachable_caps_plus C s; \<not>is_sealed_method CC c';
      is_sentry_method CC (seal_method CC c' otype) \<or> is_indirect_sentry_method CC (seal_method CC c' otype)\<rbrakk> \<Longrightarrow>
     seal_method CC c' otype \<in> reachable_caps_plus C s"
| Unseal:
    "\<lbrakk>c' \<in> reachable_caps_plus C s; c'' \<in> reachable_caps_plus C s;
      is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; is_sealed_method CC c'; permits_unseal_method CC c'';
      get_obj_type_method CC c' = get_cursor_method CC c'';
      get_cursor_method CC c'' \<in> get_mem_region CC c''\<rbrakk> \<Longrightarrow>
     clear_global_unless CC (is_global_method CC c'') (unseal_method CC c') \<in> reachable_caps_plus C s"

lemma plus_subset_reachable_caps_plus:
  "C \<subseteq> reachable_caps_plus C s"
  by (auto intro: reachable_caps_plus.Plus)

lemma reachable_caps_subset_plus:
  "reachable_caps s \<subseteq> reachable_caps_plus C s"
proof
  fix c
  assume "c \<in> reachable_caps s"
  then show "c \<in> reachable_caps_plus C s"
  proof induction
    case (Mem addr c vaddr c')
    then show ?case
      by (blast intro: reachable_caps_plus.Mem)
  qed (auto intro: reachable_caps_plus.intros)
qed

lemma reachable_caps_plus_subset:
  assumes "C \<subseteq> reachable_caps s"
  shows "reachable_caps_plus C s \<subseteq> reachable_caps s"
proof
  fix c
  assume "c \<in> reachable_caps_plus C s"
  then show "c \<in> reachable_caps s"
  proof induction
    case (Mem addr c vaddr c')
    then show ?case by - (rule reachable_caps.Mem; auto)
  next
    case (Plus c)
    then show ?case using assms by auto
  qed (auto intro: reachable_caps.intros)
qed

lemma reachable_caps_plus_subset_eq:
  assumes "C \<subseteq> reachable_caps s"
  shows "reachable_caps_plus C s = reachable_caps s"
  using assms reachable_caps_subset_plus reachable_caps_plus_subset
  by blast

lemma reachable_caps_plus_empty_eq[simp]:
  "reachable_caps_plus {} s = reachable_caps s"
  by (intro reachable_caps_plus_subset_eq) blast

lemma reachable_caps_plus_member_mono:
  assumes "c \<in> reachable_caps_plus C s" and "C \<subseteq> C'"
  shows "c \<in> reachable_caps_plus C' s"
proof (use assms in induction)
  case (Mem addr c vaddr c')
  then show ?case
    by (intro reachable_caps_plus.Mem[where c = c]) auto
next
  case (Plus c)
  then show "c \<in> reachable_caps_plus C' s"
    using assms
    by (intro reachable_caps_plus.Plus) auto
qed (auto intro: reachable_caps_plus.intros)

lemma reachable_caps_plus_mono:
  assumes "C \<subseteq> C'"
  shows "reachable_caps_plus C s \<subseteq> reachable_caps_plus C' s"
  using assms
  by (auto intro: reachable_caps_plus_member_mono)

lemma get_reg_val_s_run_trace_cases:
  assumes s': "s_run_trace t s = Some s'"
  obtains (Init) "get_reg_val r s' = get_reg_val r s"
  | (Update) j v where "get_reg_val r s' = Some v" and "t ! j = E_write_reg r v" and "j < length t"
proof (use s' in \<open>induction rule: runTraceS_rev_induct\<close>)
  case (Step t e s'' s')
  note Init = Step(4)
  note Update = Step(5)
  from \<open>s_emit_event e s'' = Some s'\<close>
  consider (Nop) "get_reg_val r s' = get_reg_val r s''"
    | (Write) v where "e = E_write_reg r v" and "get_reg_val r s' = Some v"
  proof (cases rule: emitEventS_update_cases)
    case (Write_reg r' v rs')
    then show ?thesis
      using that
      by (cases "r' = r") (auto simp: read_absorb_write read_ignore_write)
  qed (auto simp: put_mem_bytes_def Let_def)
  then show ?thesis
  proof cases
    case Nop
    show ?thesis
    proof (rule Step.IH)
      assume "get_reg_val r s'' = get_reg_val r s"
      with Nop show ?thesis
        by (intro Init) auto
    next
      fix v j
      assume "get_reg_val r s'' = Some v" and "t ! j = E_write_reg r v" "j < length t"
      with Nop show ?thesis
        by (intro Update[of v j]) (auto simp: nth_append)
    qed
  next
    case (Write v)
    then show ?thesis
      by (intro Update[of v "length t"]) auto
  qed
qed auto

lemma reads_reg_cap_at_idx_provenance[consumes 5]:
  assumes r: "t ! i = E_read_reg r v" and c: "c \<in> caps_of_regval ISA v" and tag: "is_tagged_method CC c"
    and i: "i < length t" and s': "s_run_trace t s = Some s'"
  obtains (Initial) "c \<in> get_reg_caps r s"
  | (Update) j where "c \<in> writes_reg_caps CC (caps_of_regval ISA) (t ! j)"
      and "writes_to_reg (t ! j) = Some r" and "j < i"
proof -
  from s' i obtain s1 s2
    where s1: "s_run_trace (take i t) s = Some s1"
      and s2: "s_emit_event (t ! i) s1 = Some s2"
    by (blast elim: runTraceS_nth_split)
  from s2 c r tag have "c \<in> get_reg_caps r s1"
    by (auto simp: bind_eq_Some_conv split: option.splits if_splits)
  with s1 Update show thesis using i
  proof (induction "take i t" s1 arbitrary: i t rule: runTraceS_rev_induct)
    case Init
    then show ?case by (intro Initial)
  next
    case (Step t' e s'' s' i t)
    then obtain j where j: "i = Suc j" by (cases i) auto
    then have t': "t' = take j t" and e: "e = t ! j"
      using Step by (auto simp: take_hd_drop[symmetric] hd_drop_conv_nth)
    note IH = Step(3)[of j t]
    note Update = Step(5)
    note i = \<open>i < length t\<close>
    show ?case
    proof (use \<open>s_emit_event e s'' = Some s'\<close> in \<open>cases rule: emitEventS_update_cases\<close>)
      case (Write_mem wk addr sz v tag res)
      then have c: "c \<in> get_reg_caps r s''"
        using Step
        by (auto simp: put_mem_bytes_def bind_eq_Some_conv Let_def)
      show ?thesis
        by (rule IH) (use c t' i j Update in \<open>auto\<close>)
    next
      case (Write_reg r' v rs')
      show ?thesis
      proof cases
        assume "r' = r"
        then show ?thesis
          using Write_reg e j \<open>c \<in> get_reg_caps r s'\<close>
          by (intro Update[of j]) (auto simp: read_absorb_write)
      next
        assume "r' \<noteq> r"
        show ?thesis
          by (rule IH)
             (use \<open>r' \<noteq> r\<close> Write_reg e t' i j \<open>c \<in> get_reg_caps r s'\<close> Update in
              \<open>auto simp: read_ignore_write\<close>)
      qed
    next
      case Read
      show ?thesis
        by (rule IH) (use Read Step.prems t' i j Update in \<open>auto\<close>)
    qed
  qed
qed

lemma reads_reg_cap_at_idx_from_initial:
  assumes r: "t ! i = E_read_reg r v" and c: "c \<in> caps_of_regval ISA v" and tag: "is_tagged_method CC c"
    and s': "s_run_trace t s = Some s'" and i: "i < length t"
    and "\<not> cap_reg_written_before_idx CC ISA i r t"
  shows "c \<in> get_reg_caps r s"
  using assms
  by (elim reads_reg_cap_at_idx_provenance)
     (auto simp: cap_reg_written_before_idx_def writes_reg_caps_at_idx_def)

lemma available_caps_mono:
  assumes j: "j < i"
  shows "available_caps CC ISA use_mem_caps j t \<subseteq> available_caps CC ISA use_mem_caps i t"
proof -
  have "available_caps CC ISA use_mem_caps j t \<subseteq> available_caps CC ISA use_mem_caps (Suc (j + k)) t" for k
    by (induction k) (auto simp: available_caps_Suc image_iff subset_iff)
  then show ?thesis using assms less_iff_Suc_add[of j i] by blast
qed

lemma reads_reg_cap_non_privileged_accessible[intro]:
  assumes "c \<in> caps_of_regval ISA v" and "t ! j = E_read_reg r v"
    and "\<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<notin> read_privileged_regs ISA"
    and "is_tagged_method CC c"
    and "j < i"
    and "j < length t"
  shows "c \<in> available_caps CC ISA use_mem_caps i t"
proof -
  from assms have c: "c \<in> available_caps CC ISA use_mem_caps (Suc j) t"
    by (auto simp: bind_eq_Some_conv image_iff available_caps_def available_reg_caps.simps)
  consider "i = Suc j" | "Suc j < i" using \<open>j < i\<close>
    by (cases "i = Suc j") auto
  then show "c \<in> available_caps CC ISA use_mem_caps i t"
    using c available_caps_mono[of "Suc j" i use_mem_caps t]
    by cases auto
qed

lemma system_access_permitted_at_idx_available_caps:
  assumes "system_access_permitted_before_idx CC ISA i t"
  obtains c where "c \<in> available_caps CC ISA use_mem_caps i t" and "is_tagged_method CC c"
    and "\<not>is_sealed_method CC c" and "permits_system_access_method CC c"
  using assms
  by (auto simp: system_access_permitted_before_idx_def; blast)

lemma writes_reg_cap_nth_provenance[consumes 5]:
  assumes "t ! i = E_write_reg r v" and "c \<in> caps_of_regval ISA v"
    and "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t"
    and "i < length t"
    and tagged: "is_tagged_method CC c"
  obtains (Accessible) "c \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t)"
  | (Exception) v' r' j where "c \<in> exception_targets_at_idx ISA i t" (* "leq_cap CC c c'"*)
    (*and "t ! j = E_read_reg r' v'" and "j < i"*) (*and "c' \<in> caps_of_regval ISA v'"*)
    (*and "r' \<in> KCC ISA"*) and "r \<in> PCC ISA" and "has_ex"
  | (Sentry) cs where "c \<in> inv_caps" and "cs \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t)"
    and "is_sentry_method CC cs" and "is_sealed_method CC cs"
    and "leq_cap CC c (unseal_method CC cs)" and "r \<in> PCC ISA"
  | (IndirectSentry) cs where "c \<in> inv_indirect_caps" and "cs \<in> derivable (initial_caps \<union> available_reg_caps CC ISA i t)"
    and "is_indirect_sentry_method CC cs" and "is_sealed_method CC cs"
    and "leq_cap CC c (unseal_method CC cs)" and "r \<in> IDC ISA"
  | (CCall) cc cd where "c \<in> inv_caps" and "invokable CC cc cd"
    and "cc \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t)"
    and "cd \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t)"
    and "(r \<in> PCC ISA \<and> leq_cap CC c (unseal_method CC cc)) \<or>
         (r \<in> IDC ISA \<and> leq_cap CC c (unseal_method CC cd))"
  | (Indirect) c' where "c \<in> inv_caps"
    and "c' \<in> derivable (initial_caps \<union> available_mem_caps CC ISA i t)"
    and "(leq_cap CC c c' \<and> r \<in> PCC ISA \<union> IDC ISA) \<or>
         (leq_cap CC c (unseal_method CC c') \<and> is_sealed_method CC c' \<and> is_sentry_method CC c' \<and> r \<in> PCC ISA)"
  using assms
  unfolding cheri_axioms_def
  by (fastforce elim!: store_cap_reg_axiomE[where i = i]
                simp:  writes_reg_caps_at_idx_def cap_derivable_iff_derivable eq_commute[where b = "t ! j" for t j])

lemma get_mem_cap_run_trace_cases:
  assumes c: "get_mem_cap addr (tag_granule ISA) s' = Some c"
    and s': "s_run_trace t s = Some s'"
    and tagged: "is_tagged_method CC c"
    and aligned: "address_tag_aligned ISA addr"
    and axiom: "store_tag_axiom CC ISA t"
  obtains (Initial)  "get_mem_cap addr (tag_granule ISA) s = Some c"
  | (Update) k wk bytes r where "k < length t"
    and "t ! k = E_write_memt wk addr (tag_granule ISA) bytes B1 r"
    and "cap_of_mem_bytes_method CC bytes B1 = Some c"
proof (use s' c axiom in \<open>induction rule: runTraceS_rev_induct\<close>)
  case (Step t e s'' s')
  note Update = Step.prems(2)
  have axiom: "store_tag_axiom CC ISA t"
    using \<open>store_tag_axiom CC ISA (t @ [e])\<close>
    by (auto simp: store_tag_axiom_def writes_mem_val_at_idx_def nth_append bind_eq_Some_conv split: if_splits; metis less_SucI)
  have IH: "thesis" if "get_mem_cap addr (tag_granule ISA) s'' = Some c"
  proof (rule Step.IH[OF _ _ that axiom])
    assume "get_mem_cap addr (tag_granule ISA) s = Some c"
    then show thesis by (rule Initial)
  next
    fix k wk bytes r
    assume "k < length t" and "t ! k = E_write_memt wk addr (tag_granule ISA) bytes B1 r"
      and "cap_of_mem_bytes_method CC bytes B1 = Some c"
    then show thesis
      by (intro Update[of k wk bytes r]) (auto simp: nth_append)
  qed
  obtain v tag
    where v: "get_mem_bytes addr (tag_granule ISA) s' = Some (v, tag)"
      and cv: "cap_of_mem_bytes_method CC v tag = Some c"
    using \<open>get_mem_cap addr (tag_granule ISA) s' = Some c\<close>
    by (auto simp: bind_eq_Some_conv bool_of_bitU_def split: if_splits)
  then have tag: "tag = B1" using tagged by auto
  from \<open>s_emit_event e s'' = Some s'\<close> show thesis
  proof (cases rule: emitEventS_update_cases)
    case (Write_mem wk addr' sz' v' tag' r)
    have sz': "tag' = B1 \<longrightarrow> (address_tag_aligned ISA addr' \<and> sz' = tag_granule ISA)"
      and len_v': "length v' = sz'"
      using \<open>store_tag_axiom CC ISA (t @ [e])\<close> Write_mem
      by (auto simp: store_tag_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv nth_append split: if_splits)
    show ?thesis
    proof cases
      assume addr_disj: "{addr..<tag_granule ISA + addr} \<inter> {addr'..<sz' + addr'} = {}"
      then have "get_mem_bytes addr (tag_granule ISA) s'' = get_mem_bytes addr (tag_granule ISA) s'"
        using Write_mem len_v'
        by (intro get_mem_bytes_cong) (auto simp: memstate_put_mem_bytes tagstate_put_mem_bytes)
      then show thesis
        using v cv tag
        by (intro IH) auto
    next
      assume addr_overlap: "{addr..<tag_granule ISA + addr} \<inter> {addr'..<sz' + addr'} \<noteq> {}"
      then have tag': "tag' = B1"
      proof -
        obtain addr''
          where addr_orig: "addr'' \<in> {addr..<tag_granule ISA + addr}"
            and addr_prime: "addr'' \<in> {addr'..<sz' + addr'}"
          using addr_overlap
          by blast
        have "tagstate s' addr'' = Some B1"
          using addr_orig get_mem_bytes_tagged_tagstate[OF v[unfolded tag]]
          by auto
        then show "tag' = B1"
          using addr_prime Write_mem len_v'
          by (auto simp: tagstate_put_mem_bytes)
      qed
      with addr_overlap aligned sz' have addr': "addr' = addr"
        by (auto simp: address_tag_aligned_def dvd_def mult_Suc_right[symmetric]
                 simp del: mult_Suc_right)
      then have v': "v' = v"
        using v tag tag' sz' len_v' Write_mem
        by (auto simp: get_mem_bytes_put_mem_bytes_same_addr)
      then show thesis
        using Write_mem cv tag' addr' sz' tag
        by (intro Step.prems(2)[of "length t"]) (auto simp: writes_mem_cap_def)
    qed
  next
    case (Write_reg r v rs')
    with \<open>get_mem_cap addr (tag_granule ISA) s' = Some c\<close> show thesis
      by (auto intro: IH simp: get_mem_bytes_def)
  next
    case Read
    with \<open>get_mem_cap addr (tag_granule ISA) s' = Some c\<close> show thesis
      by (auto intro: IH)
  qed
qed auto

lemma reads_mem_cap_at_idx_provenance:
  assumes read: "t ! i = E_read_memt rk addr (tag_granule ISA) (bytes, B1)"
    and c: "cap_of_mem_bytes_method CC bytes B1 = Some c"
    and s': "s_run_trace t s = Some s'"
    and axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_mem_caps inv_caps t"
    and i: "i < length t"
    and tagged: "is_tagged_method CC c"
    and aligned: "address_tag_aligned ISA addr"
  obtains (Initial) "get_mem_cap addr (tag_granule ISA) s = Some c"
  | (Update) k wk bytes' r where "k < i"
    and "t ! k = E_write_memt wk addr (tag_granule ISA) bytes' B1 r"
    and "cap_of_mem_bytes_method CC bytes' B1 = Some c"
proof -
  obtain s''
    where s'': "s_run_trace (take i t) s = Some s''"
      and c': "get_mem_cap addr (tag_granule ISA) s'' = Some c"
    using s' i read c tagged
    by (cases rule: runTraceS_nth_split; cases "t ! i")
       (auto simp: bind_eq_Some_conv reads_mem_cap_def split: if_splits)
  have "store_tag_axiom CC ISA (take i t)"
    using axioms
    by (fastforce simp: cheri_axioms_def store_tag_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv)
  with c' s'' tagged aligned show thesis
    by (cases rule: get_mem_cap_run_trace_cases) (auto intro: that)
qed

lemmas derivable_Un2_refl = subset_trans[OF derivable_refl Un_upper2[THEN derivable_mono]]
lemmas derivable_Un1_refl = subset_trans[OF derivable_refl Un_upper1[THEN derivable_mono]]

lemma derivable_available_caps_subseteq_reachable_caps:
  assumes axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t"
    and t: "s_run_trace t s = Some s'"
  shows "derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t) \<subseteq> reachable_caps_plus initial_caps s"
proof (induction i rule: less_induct)
  case (less i)
  show ?case proof
    fix c
    assume "c \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t)"
    then show "c \<in> reachable_caps_plus initial_caps s"
    proof induction
      fix c
      assume "c \<in> initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t"
      moreover have "c \<in> reachable_caps_plus initial_caps s"
        if "c \<in> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t"
      proof (use that in \<open>cases rule: available_caps_cases\<close>)
        case (Reg r v j)
        from Reg(1-4) t
        show ?thesis
        proof (cases rule: reads_reg_cap_at_idx_provenance)
          case Initial
          show ?thesis
          proof cases
            assume r: "r \<in> read_privileged_regs ISA"
            then obtain c' where c': "c' \<in> reachable_caps_plus initial_caps s" and "is_tagged_method CC c'"
              and "\<not>is_sealed_method CC c'" and p: "permits_system_access_method CC c'"
              using Reg less.IH[OF \<open>j < i\<close>]
              using derivable_Un2_refl[of "available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) j t"]
              by (auto elim!: system_access_permitted_at_idx_available_caps)
            then show ?thesis
              using Reg
              by (auto intro: reachable_caps_plus.SysReg[OF Initial r c'])
          next
            assume "r \<notin> read_privileged_regs ISA"
            then show ?thesis using Initial Reg by (auto intro: reachable_caps_plus.Reg)
          qed
        next
          case (Update k)
          then obtain v where e: "t ! k = E_write_reg r v" and c_v: "c \<in> caps_of_regval ISA v" and k: "k < length t"
            using \<open>j < length t\<close>
            by auto
          then have r: "cap_reg_written_before_idx CC ISA j r t"
            using \<open>is_tagged_method CC c\<close> \<open>k < j\<close>
            by (fastforce simp: cap_reg_written_before_idx_def)
          from e c_v axioms k \<open>is_tagged_method CC c\<close> \<open>k < j\<close> \<open>j < i\<close> r Reg(6) less.IH[of k]
          show ?thesis
            by (cases rule: writes_reg_cap_nth_provenance) auto
        qed
      next
        case (Mem wk paddr bytes j sz)
        note read = \<open>t ! j = E_read_memt wk paddr sz (bytes, B1)\<close>
        note bytes = \<open>cap_of_mem_bytes_method CC bytes B1 = Some c\<close>
        have "\<not>translation_event_at_idx ISA j t"
          using Mem
          by (auto simp: translation_event_at_idx_def)
        then obtain vaddr c'
          where vaddr: "translate_address ISA vaddr Load (take j t) = Some paddr"
            and c': "c' \<in> derivable (initial_caps \<union> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) j t)"
                    "is_tagged_method CC c'"
                    "is_sealed_method CC c' \<longrightarrow> is_indirect_sentry_method CC c' \<and> unseal_method CC c' \<in> inv_indirect_caps"
                    "set (address_range vaddr sz) \<subseteq> get_mem_region CC c'"
                    "permits_load_method CC c'"
                    "permits_load_cap_method CC c'"
            and sz: "sz = tag_granule ISA"
            and aligned: "address_tag_aligned ISA paddr"
          using read t axioms \<open>j < length t\<close> \<open>is_tagged_method CC c\<close> \<open>inv_indirect_caps = {} \<and> use_mem_caps\<close>
          unfolding cheri_axioms_def
          by (auto elim!: load_mem_axiomE simp: reads_mem_val_at_idx_def cap_derivable_iff_derivable)
        have s_vaddr: "s_translate_address vaddr Load s = Some paddr"
          using vaddr t \<open>j < length t\<close>
          by (blast intro: translate_address_sound[of "take j t"] elim: runTraceS_nth_split)
        from read[unfolded sz] bytes t axioms \<open>j < length t\<close> \<open>is_tagged_method CC c\<close> aligned
        show ?thesis
        proof (cases rule: reads_mem_cap_at_idx_provenance)
          case Initial
          then show ?thesis
            using Mem s_vaddr less.IH[of j] c' aligned sz
            by (intro reachable_caps_plus.Mem[of paddr s c vaddr c'])
               (auto simp: bind_eq_Some_conv translate_address_tag_aligned_iff permits_cap_load_def split: if_splits)
        next
          case (Update k wk bytes' r)
          then show ?thesis
            using axioms \<open>is_tagged_method CC c\<close> \<open>j < length t\<close> \<open>j < i\<close> less.IH[of k]
            unfolding cheri_axioms_def store_cap_mem_axiom_def
            by (auto simp: writes_mem_cap_at_idx_def writes_mem_cap_Some_iff bind_eq_Some_conv cap_derivable_iff_derivable)
        qed
      qed
      ultimately show "c \<in> reachable_caps_plus initial_caps s"
        by (auto intro: reachable_caps_plus.Plus)
    qed (auto intro: reachable_caps_plus.intros)
  qed
qed

lemma put_regval_get_mem_cap:
  assumes s': "put_reg_val r v s = Some s'"
    and "s_translate_address addr acctype s' = s_translate_address addr acctype s"
  shows "get_mem_cap addr sz s' = get_mem_cap addr sz s"
  using assms by (auto cong: bind_option_cong simp: get_mem_bytes_def)

text \<open>System register and address translation invariants\<close>

definition system_access_reachable_plus :: "'cap set \<Rightarrow> 'regs sequential_state \<Rightarrow> bool" where
  "system_access_reachable_plus C s \<equiv> \<exists>c \<in> reachable_caps_plus C s.
     permits_system_access_method CC c \<and> is_tagged_method CC c \<and> \<not>is_sealed_method CC c"

abbreviation "system_access_reachable s \<equiv> system_access_reachable_plus {} s"

lemma system_access_reachable_plus_mono:
  assumes "system_access_reachable_plus C s"
    and "C \<subseteq> C'"
  shows "system_access_reachable_plus C' s"
  using assms(1) reachable_caps_plus_mono[OF assms(2)]
  by (auto simp: system_access_reachable_plus_def)

lemma system_access_reachable_plus_reachable_caps_mono:
  assumes "system_access_reachable_plus C s"
    and "reachable_caps_plus C s \<subseteq> reachable_caps_plus C' s'"
  shows "system_access_reachable_plus C' s'"
  using assms
  by (auto simp: system_access_reachable_plus_def)

lemma system_access_reachable_plus_subset_reachable_caps_iff:
  assumes "C \<subseteq> reachable_caps s"
  shows "system_access_reachable_plus C s = system_access_reachable s"
  by (auto simp: system_access_reachable_plus_def reachable_caps_plus_subset_eq[OF assms])

definition priv_regs_invariant :: "bool \<Rightarrow> 'regs sequential_state \<Rightarrow> 'regs sequential_state \<Rightarrow> bool" where
  "priv_regs_invariant has_ex s0 s \<equiv>
     (\<forall>r. r \<in> write_privileged_regs ISA \<and> (r \<in> write_exception_regs ISA \<longrightarrow> \<not>has_ex) \<longrightarrow>
          get_reg_val r s = get_reg_val r s0)"

lemma equivp_priv_regs_invariant: "equivp (priv_regs_invariant has_ex)"
  by (intro equivpI reflpI sympI transpI) (auto simp: priv_regs_invariant_def)

definition addr_trans_invariant_plus :: "'cap set \<Rightarrow> bool \<Rightarrow> 'regs sequential_state \<Rightarrow> 'regs sequential_state \<Rightarrow> bool" where
  "addr_trans_invariant_plus C has_ex s0 s \<equiv>
     (system_access_reachable_plus C s0 \<or> priv_regs_invariant has_ex s0 s) \<longrightarrow>
     (\<forall>vaddr acctype. s_translate_address vaddr acctype s = s_translate_address vaddr acctype s0)"

abbreviation "addr_trans_invariant has_ex s0 s \<equiv> addr_trans_invariant_plus {} has_ex s0 s"

lemma addr_trans_invariant_plus_refl[intro, simp]:
  "addr_trans_invariant_plus C has_ex s s"
  by (auto simp: addr_trans_invariant_plus_def)

lemma addr_trans_invariant_plus_antimono:
  assumes "addr_trans_invariant_plus C has_ex s0 s"
    and "C' \<subseteq> C"
  shows "addr_trans_invariant_plus C' has_ex s0 s"
  using assms(1) reachable_caps_plus_mono[OF assms(2)] system_access_reachable_plus_reachable_caps_mono
  by (auto simp: addr_trans_invariant_plus_def)

lemma addr_trans_invariant_plus_subset_reachable_caps_eq:
  assumes "C \<subseteq> reachable_caps s0"
  shows "addr_trans_invariant_plus C has_ex s0 = addr_trans_invariant has_ex s0"
  by (rule ext, unfold addr_trans_invariant_plus_def)
     (auto simp: system_access_reachable_plus_subset_reachable_caps_iff[OF assms])

lemma s_invariant_holds_addr_trans_append_left:
  assumes "s_invariant_holds (addr_trans_invariant_plus C has_ex s) (t1 @ t2) s"
  shows "s_invariant_holds (addr_trans_invariant_plus C has_ex s) t1 s"
  using assms
  by (auto simp: s_invariant_append)

lemma system_access_reachable_if_permitted:
  assumes axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t"
    and t: "s_run_trace t s = Some s'"
    and asr: "system_access_permitted_before_idx CC ISA i t"
  shows "system_access_reachable_plus initial_caps s"
proof -
  from asr obtain c where *: "c \<in> available_caps CC ISA (inv_indirect_caps = {} \<and> use_mem_caps) i t"
    and c: "permits_system_access_method CC c" "is_tagged_method CC c" "\<not>is_sealed_method CC c"
    by (auto elim!: system_access_permitted_at_idx_available_caps)
  then have "c \<in> reachable_caps_plus initial_caps s"
    using derivable_available_caps_subseteq_reachable_caps[OF axioms t]
    using derivable_Un2_refl[of _ initial_caps]
    by auto
  then show ?thesis
    using c
    by (auto simp: system_access_reachable_plus_def)
qed

lemma no_asr_priv_reg_invariant:
  assumes axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t"
    and t: "s_run_trace t s = Some s'"
    and no_asr: "\<not>system_access_reachable_plus initial_caps s"
    and r: "r \<in> write_privileged_regs ISA \<and> (r \<in> write_exception_regs ISA \<longrightarrow> \<not>has_ex)"
  shows "get_reg_val r s = get_reg_val r s'"
proof (use t in \<open>cases rule: get_reg_val_s_run_trace_cases[where r = r]\<close>)
  case Init
  then show ?thesis ..
next
  case (Update j v)
  then have "system_access_permitted_before_idx CC ISA j t"
    using t axioms r
    unfolding cheri_axioms_def write_reg_axiom_def
    by fastforce
  from system_access_reachable_if_permitted[OF axioms t this] no_asr
  have "False"
    by auto
  then show ?thesis ..
qed

lemma no_asr_priv_regs_invariant:
  assumes axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t"
    and t: "s_run_trace t s = Some s'"
    and no_asr: "\<not>system_access_reachable_plus initial_caps s"
  shows "s_invariant_holds (priv_regs_invariant has_ex s) t s"
proof (use t in \<open>induction rule: take_s_invariant_holdsI\<close>)
  case Init
  then show ?case
    by (auto simp: priv_regs_invariant_def)
next
  case (Inv n s'')
  then show ?case
    using no_asr_priv_reg_invariant[OF cheri_axioms_take[where n = n, OF axioms]] no_asr
    by (auto simp: priv_regs_invariant_def)
qed

lemma s_invariant_holds_addr_trans_append_right:
  assumes inv: "s_invariant_holds (addr_trans_invariant_plus C has_ex s) (t1 @ t2) s"
    and t: "s_run_trace t1 s = Some s'"
    and axioms: "cheri_axioms CC ISA is_fetch has_ex initial_caps use_mem_caps inv_caps inv_indirect_caps t1"
    and caps: "reachable_caps_plus C' s' \<subseteq> reachable_caps_plus C s"
    and initial_caps: "initial_caps \<subseteq> C"
  shows "s_invariant_holds (addr_trans_invariant_plus C' has_ex s') t2 s'"
proof -
  have regs: "priv_regs_invariant has_ex s s'" if "\<not>system_access_reachable_plus C s"
  proof -
    from that initial_caps have "\<not>system_access_reachable_plus initial_caps s"
      by (auto intro: system_access_reachable_plus_mono)
    from no_asr_priv_regs_invariant[OF axioms t this] t
    show ?thesis
      by (auto dest: s_invariant_run_trace_eq)
  qed
  have "s_invariant_holds (addr_trans_invariant_plus C has_ex s) t2 s'"
    using inv t
    by (auto simp: s_invariant_append dest: s_invariant_run_trace_eq)
  then show ?thesis
    using regs system_access_reachable_plus_reachable_caps_mono[OF _ caps]
    using regs[THEN equivp_priv_regs_invariant[THEN equivp_transp]]
    by (elim s_invariant_holds_weaken) (auto simp: addr_trans_invariant_plus_def)
qed

lemma get_reg_cap_intra_domain_trace_reachable:
  assumes r: "c \<in> get_reg_caps r s'"
    (*and t: "hasTrace t (instr_sem ISA instr)"*) and s': "s_run_trace t s = Some s'"
    and axioms: "cheri_axioms CC ISA is_fetch False initial_caps use_mem_caps invoked_caps invoked_indirect_caps t"
    and C: "initial_caps \<union> invoked_caps \<union> invoked_indirect_caps \<subseteq> C"
    (*and no_exception: "\<not>hasException t (instr_sem ISA instr)"
    and no_ccall: "invoked_caps ISA instr t = {}"*)
    and tag: "is_tagged_method CC c"
    and priv: "r \<in> read_privileged_regs ISA \<longrightarrow> system_access_reachable_plus C s"
  (* TODO: shows "c \<in> reachable_caps s \<or> (r \<in> (PCC ISA \<union> IDC ISA) \<and> c \<in> invoked_caps)" *)
  shows "c \<in> reachable_caps_plus C s"
proof -
  from r obtain v where v: "get_reg_val r s' = Some v" and c: "c \<in> caps_of_regval ISA v"
    by (auto simp: bind_eq_Some_conv split: option.splits)
  from s' show "c \<in> reachable_caps_plus C s"
  proof (cases rule: get_reg_val_s_run_trace_cases[where r = r])
    case Init
    show ?thesis
    proof cases
      assume r: "r \<in> read_privileged_regs ISA"
      with priv obtain c' where c': "c' \<in> reachable_caps_plus C s"
        and "permits_system_access_method CC c'"
        and "is_tagged_method CC c'" and "\<not>is_sealed_method CC c'"
        using reachable_caps_plus_mono[OF C]
        by (auto simp: system_access_reachable_plus_def)
      then show "c \<in> reachable_caps_plus C s"
        using Init c tag v
        by (intro reachable_caps_plus.SysReg[OF _ r c']) auto
    next
      assume "r \<notin> read_privileged_regs ISA"
      then have "c \<in> reachable_caps s"
        using Init c tag v
        by (intro reachable_caps.Reg) auto
      then show ?thesis
        using reachable_caps_subset_plus
        by blast
    qed
  next
    case (Update j)
    show ?thesis
    proof cases
      assume "c \<in> initial_caps \<union> invoked_caps \<union> invoked_indirect_caps"
      then show "c \<in> reachable_caps_plus C s"
        using C
        by (intro reachable_caps_plus.Plus) auto
    next
      assume c_not_inv: "c \<notin> initial_caps \<union> invoked_caps \<union> invoked_indirect_caps"
      from Update have "c \<in> writes_reg_caps CC (caps_of_regval ISA) (t ! j)"
        and "writes_to_reg (t ! j) = Some r"
        using tag c v
        by auto
      then have "c \<in> derivable (initial_caps \<union> available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) j t)"
        using axioms tag \<open>j < length t\<close> c_not_inv
        unfolding cheri_axioms_def
        by (auto elim!: store_cap_reg_axiomE simp: cap_derivable_iff_derivable)
      moreover have "derivable (initial_caps \<union> available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) j t) \<subseteq> reachable_caps_plus initial_caps s"
        using axioms s'
        by (intro derivable_available_caps_subseteq_reachable_caps)
      ultimately show ?thesis
        using reachable_caps_plus_mono[of initial_caps] C
        by auto
    qed
  qed
qed

lemma reachable_caps_plus_trace_intradomain_monotonicity:
  assumes axioms: "cheri_axioms CC ISA is_fetch False initial_caps use_mem_caps invoked_caps invoked_indirect_caps t"
    and s': "s_run_trace t s = Some s'"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) False s) t s"
  shows "reachable_caps_plus C s' \<subseteq> reachable_caps_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) s"
proof
  fix c
  assume "c \<in> reachable_caps_plus C s'"
  then show "c \<in> reachable_caps_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) s"
  proof induction
    case (Reg r c)
    then show ?case
      using axioms s'
      by (intro get_reg_cap_intra_domain_trace_reachable) auto
  next
    case (SysReg c r c')
    then show ?case
      using axioms s'
      by (intro get_reg_cap_intra_domain_trace_reachable) (auto simp: system_access_reachable_plus_def)
  next
    case (Mem addr c vaddr c')
    then have c: "get_mem_cap addr (tag_granule ISA) s' = Some c"
      and aligned: "address_tag_aligned ISA addr"
      by (auto split: if_splits)
    have axiom: "store_tag_axiom CC ISA t"
      using axioms
      by (auto simp: cheri_axioms_def)
    from c s' \<open>is_tagged_method CC c\<close> aligned axiom show ?case
    proof (cases rule: get_mem_cap_run_trace_cases)
      case Initial
      have "s_translate_address vaddr Load s' = s_translate_address vaddr Load s"
      proof -
        have "addr_trans_invariant_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) False s s'"
          using addr_trans_inv
          by (auto dest: s_invariant_run_trace_eq[OF _ s'])
        moreover have "priv_regs_invariant False s s'"
          if "\<not>system_access_reachable_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) s"
          using no_asr_priv_regs_invariant[OF axioms s'] that
          by (auto dest: s_invariant_run_trace_eq[OF _ s'] intro: system_access_reachable_plus_mono)
        ultimately show ?thesis
          by (auto simp: addr_trans_invariant_plus_def)
      qed
      then show ?thesis
        using Initial Mem
        by (intro reachable_caps_plus.Mem[of addr s c vaddr c']) (auto split: if_splits)
    next
      case (Update k wk bytes r)
      have "derivable (initial_caps \<union> available_caps CC ISA (invoked_indirect_caps = {} \<and> use_mem_caps) k t) \<subseteq> reachable_caps_plus initial_caps s"
        using assms axioms
        by (intro derivable_available_caps_subseteq_reachable_caps)
      then have "c \<in> reachable_caps_plus initial_caps s"
        using Update \<open>is_tagged_method CC c\<close> axioms
        unfolding cheri_axioms_def store_cap_mem_axiom_def cap_derivable_iff_derivable
        by (auto simp: writes_mem_cap_at_idx_def writes_mem_cap_Some_iff)
      then show "c \<in> reachable_caps_plus (C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)) s"
        using reachable_caps_plus_mono[of initial_caps "C \<union> initial_caps \<union> (invoked_caps \<union> invoked_indirect_caps)"]
        by blast
    qed
  qed (auto intro: reachable_caps_plus.intros)
qed

abbreviation "invoked_instr_caps instr t \<equiv> invokes_caps ISA instr t \<union> invokes_indirect_caps ISA instr t"

lemma hasTrace_instr_cheri_axioms:
  assumes t: "hasTrace t (instr_sem ISA instr)"
    and ci: "\<forall>c \<in> reachable_caps_plus C' s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and initial_caps: "initial_caps \<subseteq> C'"
    and ta: "instr_assms instr t"
    and s': "s_run_trace (take n t) s = Some s'"
    and n: "n \<le> length t"
  shows "instr_cheri_axioms instr t n \<and> instr_available_caps_invariant instr t n"
proof (use s' n in \<open>induction n arbitrary: s'\<close>)
  case 0
  then show ?case
    using instr_cheri_axioms[OF t _ _ ta, where n = 0]
    by (auto simp: available_caps_invariant_def)
next
  case (Suc n)
  then obtain s'' where s'': "s_run_trace (take n t) s = Some s''" and n: "n \<le> length t"
    by (auto simp: take_Suc_conv_app_nth runTraceS_append_iff)
  let ?C = "available_caps CC ISA (invokes_indirect_caps ISA instr t = {} \<and> uses_mem_caps ISA instr t) n (take n t)"
  have "initial_caps \<union> ?C \<subseteq> derivable (initial_caps \<union> ?C)"
    by (rule derivable_refl)
  also have "\<dots> \<subseteq> reachable_caps_plus initial_caps s"
    using Suc.IH[OF s'' n] s''
    by (intro derivable_available_caps_subseteq_reachable_caps) auto
  also have "\<dots> \<subseteq> reachable_caps_plus C' s"
    by (rule reachable_caps_plus_mono[OF initial_caps])
  finally have "cap_invariant c" if "c \<in> initial_caps \<union> ?C" and "is_tagged_method CC c" for c
    using that ci
    by auto
  then have inv: "instr_available_caps_invariant instr t (Suc n)"
    using Suc.IH[OF s'' n]
    by (auto simp: available_caps_invariant_def less_Suc_eq)
  moreover have "instr_cheri_axioms instr t (Suc n)"
    using inv Suc.prems t ta
    by (intro instr_cheri_axioms) auto
  ultimately show ?case
    by auto
qed

lemma reachable_caps_plus_instr_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_sem ISA instr)"
    and ci: "\<forall>c \<in> reachable_caps_plus C'' s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and initial_caps: "initial_caps \<subseteq> C''"
    and ta: "instr_assms instr t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instr_raises_ex ISA instr t"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant_plus C' False s) t s"
    and C': "C \<union> initial_caps \<union> invoked_instr_caps instr t \<subseteq> C'"
  shows "reachable_caps_plus C s' \<subseteq> reachable_caps_plus C' s"
proof -
  have addr_trans_inv': "s_invariant_holds (addr_trans_invariant_plus (C \<union> initial_caps \<union> invoked_instr_caps instr t) False s) t s"
    using addr_trans_inv addr_trans_invariant_plus_antimono[OF _ C']
    by (elim s_invariant_holds_weaken) auto
  then have "reachable_caps_plus C s' \<subseteq> reachable_caps_plus (C \<union> initial_caps \<union> invoked_instr_caps instr t) s"
    using assms hasTrace_instr_cheri_axioms[OF t ci initial_caps ta, where n = "length t"]
    by (intro reachable_caps_plus_trace_intradomain_monotonicity) auto
  then show ?thesis
    using reachable_caps_plus_mono[OF C']
    by auto
qed

lemma reachable_caps_instr_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_sem ISA instr)"
    and ci: "\<forall>c \<in> reachable_caps s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and ta: "instr_assms instr t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instr_raises_ex ISA instr t"
    and invoked_caps_reachable: "invoked_instr_caps instr t \<subseteq> reachable_caps s"
    and initial_caps_reachable: "initial_caps \<subseteq> reachable_caps s"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant False s) t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof -
  have *: "initial_caps \<union> invoked_instr_caps instr t \<subseteq> reachable_caps s"
    using invoked_caps_reachable initial_caps_reachable
    by simp
  have "reachable_caps_plus {} s' \<subseteq> reachable_caps_plus ({} \<union> initial_caps \<union> invoked_instr_caps instr t) s"
    using t ci ta s' no_exception addr_trans_inv
    by (intro reachable_caps_plus_instr_trace_intradomain_monotonicity[where C'' = "initial_caps"])
       (auto simp: addr_trans_invariant_plus_subset_reachable_caps_eq[OF *]
                   reachable_caps_plus_subset_eq[OF initial_caps_reachable])
  then show ?thesis
    by (auto simp: reachable_caps_plus_subset_eq[OF *])
qed

lemma hasTrace_fetch_cheri_axioms:
  assumes t: "hasTrace t (instr_fetch ISA)"
    and ci: "\<forall>c \<in> reachable_caps_plus C' s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and initial_caps: "initial_caps \<subseteq> C'"
    and ta: "fetch_assms t"
    and s': "s_run_trace (take n t) s = Some s'"
    and n: "n \<le> length t"
  shows "fetch_cheri_axioms t n \<and> fetch_available_caps_invariant t n"
proof (use s' n in \<open>induction n arbitrary: s'\<close>)
  case 0
  then show ?case
    using fetch_cheri_axioms[OF t _ _ ta, where n = 0]
    by (auto simp: available_caps_invariant_def)
next
  case (Suc n)
  then obtain s'' where s'': "s_run_trace (take n t) s = Some s''" and n: "n \<le> length t"
    by (auto simp: take_Suc_conv_app_nth runTraceS_append_iff)
  let ?C = "available_caps CC ISA ({} = ({} :: 'cap set) \<and> True) n (take n t)"
  have "initial_caps \<union> ?C \<subseteq> derivable (initial_caps \<union> ?C)"
    by (rule derivable_refl)
  also have "\<dots> \<subseteq> reachable_caps_plus initial_caps s"
    using Suc.IH[OF s'' n] s''
    by (intro derivable_available_caps_subseteq_reachable_caps) auto
  also have "\<dots> \<subseteq> reachable_caps_plus C' s"
    by (rule reachable_caps_plus_mono[OF initial_caps])
  finally have "cap_invariant c" if "c \<in> initial_caps \<union> ?C" and "is_tagged_method CC c" for c
    using that ci
    by auto
  then have inv: "fetch_available_caps_invariant t (Suc n)"
    using Suc.IH[OF s'' n]
    by (auto simp: available_caps_invariant_def less_Suc_eq)
  moreover have "fetch_cheri_axioms t (Suc n)"
    using inv Suc.prems t ta
    by (intro fetch_cheri_axioms) auto
  ultimately show ?case
    by auto
qed

lemma reachable_caps_plus_fetch_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_fetch ISA)"
    and ci: "\<forall>c \<in> reachable_caps_plus C'' s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and initial_caps: "initial_caps \<subseteq> C''"
    and ta: "fetch_assms t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>fetch_raises_ex ISA t"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant_plus C' False s) t s"
    and C': "C \<union> initial_caps \<subseteq> C'"
  shows "reachable_caps_plus C s' \<subseteq> reachable_caps_plus C' s"
proof -
  have addr_trans_inv': "s_invariant_holds (addr_trans_invariant_plus (C \<union> initial_caps) False s) t s"
    using addr_trans_inv addr_trans_invariant_plus_antimono[OF _ C']
    by (elim s_invariant_holds_weaken) auto
  then have "reachable_caps_plus C s' \<subseteq> reachable_caps_plus (C \<union> initial_caps \<union> ({} \<union> {})) s"
    using assms hasTrace_fetch_cheri_axioms[OF t ci initial_caps(1), where n = "length t"]
    by (intro reachable_caps_plus_trace_intradomain_monotonicity) auto
  then show ?thesis
    using reachable_caps_plus_mono[OF C']
    by auto
qed

lemma reachable_caps_fetch_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_fetch ISA)"
    and ci: "\<forall>c \<in> reachable_caps s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and initial_caps: "initial_caps \<subseteq> reachable_caps s"
    and ta: "fetch_assms t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>fetch_raises_ex ISA t"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant False s) t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof -
  have "reachable_caps_plus {} s' \<subseteq> reachable_caps_plus ({} \<union> initial_caps) s"
    using assms
    by (intro reachable_caps_plus_fetch_trace_intradomain_monotonicity[where t = t and C'' = initial_caps])
       (auto simp: addr_trans_invariant_plus_subset_reachable_caps_eq[OF initial_caps]
                   reachable_caps_plus_subset_eq[OF initial_caps])
  then show ?thesis
    by (auto simp: reachable_caps_plus_subset_eq[OF initial_caps])
qed

end

section \<open>Multi-instruction monotonicity\<close>

fun fetch_execute_loop :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> ('regval, unit, 'e) monad" where
  "fetch_execute_loop ISA (Suc bound) = (instr_fetch ISA \<bind> instr_sem ISA) \<then> fetch_execute_loop ISA bound"
| "fetch_execute_loop ISA 0 = return ()"

fun instrs_raise_ex :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "instrs_raise_ex ISA (Suc bound) t =
     (\<exists>nf. consumesTrace (instr_fetch ISA) t = Some nf \<and>
          (fetch_raises_ex ISA (take nf t) \<or>
           (\<exists>instr ni.
               runTrace (take nf t) (instr_fetch ISA) = Some (Done instr) \<and>
               consumesTrace (instr_sem ISA instr) (drop nf t) = Some ni \<and>
               (instr_raises_ex ISA instr (take ni (drop nf t)) \<or>
                instrs_raise_ex ISA bound (drop ni (drop nf t))))))"
| "instrs_raise_ex ISA 0 t = False"

fun instrs_invoke_caps :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> 'regval trace \<Rightarrow> 'cap set" where
  "instrs_invoke_caps ISA (Suc bound) t =
    {c. (\<exists>nf. consumesTrace (instr_fetch ISA) t = Some nf \<and>
          (\<exists>instr ni.
             runTrace (take nf t) (instr_fetch ISA) = Some (Done instr) \<and>
             consumesTrace (instr_sem ISA instr) (drop nf t) = Some ni \<and>
             (c \<in> invokes_caps ISA instr (take ni (drop nf t)) \<or>
              c \<in> instrs_invoke_caps ISA bound (drop ni (drop nf t)))))}"
| "instrs_invoke_caps ISA 0 t = {}"

lemma instrs_invoke_caps_Suc:
  assumes tf: "Run (instr_fetch ISA) tf instr" and ti: "hasTrace ti (instr_sem ISA instr)"
  shows "instrs_invoke_caps ISA (Suc n) (tf @ ti @ t') =
         invokes_caps ISA instr ti \<union> instrs_invoke_caps ISA n t'"
proof -
  from tf
  have "consumesTrace (instr_fetch ISA) (tf @ ti @ t') = Some (length tf)"
    and "runTrace tf (instr_fetch ISA) = Some (Done instr)"
    by (auto simp: runTrace_iff_Traces intro: Run_hasTrace hasTrace_consumesTrace)
  moreover from ti
  have "consumesTrace (instr_sem ISA instr) (ti @ t') = Some (length ti)"
    by (auto intro: hasTrace_consumesTrace)
  ultimately
  show ?thesis
    by auto
qed

fun instrs_invoke_indirect_caps :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> 'regval trace \<Rightarrow> 'cap set" where
  "instrs_invoke_indirect_caps ISA (Suc bound) t =
    {c. (\<exists>nf. consumesTrace (instr_fetch ISA) t = Some nf \<and>
          (\<exists>instr ni.
             runTrace (take nf t) (instr_fetch ISA) = Some (Done instr) \<and>
             consumesTrace (instr_sem ISA instr) (drop nf t) = Some ni \<and>
             (c \<in> invokes_indirect_caps ISA instr (take ni (drop nf t)) \<or>
              c \<in> instrs_invoke_indirect_caps ISA bound (drop ni (drop nf t)))))}"
| "instrs_invoke_indirect_caps ISA 0 t = {}"

lemma instrs_invoke_indirect_caps_Suc:
  assumes tf: "Run (instr_fetch ISA) tf instr" and ti: "hasTrace ti (instr_sem ISA instr)"
  shows "instrs_invoke_indirect_caps ISA (Suc n) (tf @ ti @ t') =
         invokes_indirect_caps ISA instr ti \<union> instrs_invoke_indirect_caps ISA n t'"
proof -
  from tf
  have "consumesTrace (instr_fetch ISA) (tf @ ti @ t') = Some (length tf)"
    and "runTrace tf (instr_fetch ISA) = Some (Done instr)"
    by (auto simp: runTrace_iff_Traces intro: Run_hasTrace hasTrace_consumesTrace)
  moreover from ti
  have "consumesTrace (instr_sem ISA instr) (ti @ t') = Some (length ti)"
    by (auto intro: hasTrace_consumesTrace)
  ultimately
  show ?thesis
    by auto
qed

lemma fetch_raises_ex_instrs_raise_ex:
  assumes "hasTrace tf (instr_fetch ISA)" and "fetch_raises_ex ISA tf"
  shows "instrs_raise_ex ISA (Suc n) (tf @ t')"
  using assms
  by (auto simp: hasTrace_consumesTrace)

lemma instrs_raise_ex_Suc:
  assumes tf: "Run (instr_fetch ISA) tf instr" and ti: "hasTrace ti (instr_sem ISA instr)"
  shows "instrs_raise_ex ISA (Suc n) (tf @ ti @ t') \<longleftrightarrow>
         fetch_raises_ex ISA tf \<or> instr_raises_ex ISA instr ti \<or> instrs_raise_ex ISA n t'"
proof -
  from tf
  have "consumesTrace (instr_fetch ISA) (tf @ ti @ t') = Some (length tf)"
    and "runTrace tf (instr_fetch ISA) = Some (Done instr)"
    by (auto simp: runTrace_iff_Traces intro: Run_hasTrace hasTrace_consumesTrace)
  moreover from ti
  have "consumesTrace (instr_sem ISA instr) (ti @ t') = Some (length ti)"
    by (auto intro: hasTrace_consumesTrace)
  ultimately
  show ?thesis
    by auto
qed

declare instrs_invoke_caps.simps(1)[simp del]
declare instrs_invoke_indirect_caps.simps(1)[simp del]
declare instrs_raise_ex.simps[simp del]

context CHERI_ISA_State
begin

fun instrs_assms :: "nat \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "instrs_assms (Suc n) t =
     (\<forall>nf. consumesTrace (instr_fetch ISA) t = Some nf
       \<longrightarrow> fetch_assms (take nf t)
         \<and> (\<forall>instr ni. runTrace (take nf t) (instr_fetch ISA) = Some (Done instr)
                     \<and> consumesTrace (instr_sem ISA instr) (drop nf t) = Some ni
                    \<longrightarrow> instr_assms instr (take ni (drop nf t)) \<and> instrs_assms n (drop (nf + ni) t)))"
| "instrs_assms 0 t = True"

abbreviation "invoked_instrs_caps n t \<equiv> instrs_invoke_caps ISA n t \<union> instrs_invoke_indirect_caps ISA n t"

lemma invoked_instrs_caps_Suc:
  assumes tf: "Run (instr_fetch ISA) tf instr" and ti: "hasTrace ti (instr_sem ISA instr)"
  shows "invoked_instrs_caps (Suc n) (tf @ ti @ t') =
         invoked_instr_caps instr ti \<union> invoked_instrs_caps n t'"
  using assms
  by (auto simp: instrs_invoke_caps_Suc instrs_invoke_indirect_caps_Suc)

lemma reachable_caps_plus_instrs_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (fetch_execute_loop ISA n)"
    and ci: "\<forall>c \<in> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t) s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and ta: "instrs_assms n t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instrs_raise_ex ISA n t"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant_plus (initial_caps \<union> invoked_instrs_caps n t) False s) t s"
  shows "reachable_caps s' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t) s"
proof (use assms in \<open>induction n arbitrary: s t\<close>)
  case 0
  then show ?case
    using reachable_caps_subset_plus
    by (auto simp: return_def hasTrace_iff_Traces_final)
next
  case (Suc n)
  then obtain m'
    where "(instr_fetch ISA \<bind> (\<lambda>instr. \<lbrakk>instr\<rbrakk> \<then> fetch_execute_loop ISA n), t, m') \<in> Traces"
    and m': "final m'"
    by (auto simp: hasTrace_iff_Traces_final)
  then show ?case
  proof (cases rule: bind_Traces_cases)
    case (Left m'')
    then have "hasTrace t (instr_fetch ISA)"
      using m'
      by (auto elim!: final_bind_cases) (auto simp: hasTrace_iff_Traces_final final_def)
    moreover have "s_invariant_holds (addr_trans_invariant_plus initial_caps False s) t s"
      using Suc.prems
      by (elim s_invariant_holds_weaken) (auto intro: addr_trans_invariant_plus_antimono)
    ultimately have "reachable_caps_plus {} s' \<subseteq> reachable_caps_plus ({} \<union> initial_caps) s"
      using Suc.prems fetch_raises_ex_instrs_raise_ex[where tf = t and t' = "[]"]
      using hasTrace_consumesTrace[where t = t and t' = "[]" and m = "instr_fetch ISA"]
      by (intro reachable_caps_plus_fetch_trace_intradomain_monotonicity) auto
    also have "\<dots> \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s"
      by (intro reachable_caps_plus_mono) auto
    finally show ?thesis
      by simp
  next
    case (Bind tf instr t')
    obtain s'' where s'': "s_run_trace tf s = Some s''" and t': "s_run_trace t' s'' = Some s'"
      using Bind Suc
      by (auto elim: runTraceS_appendE)
    have tf: "hasTrace tf (instr_fetch ISA)"
      using Bind
      by (auto simp: hasTrace_iff_Traces_final final_def)
    from fetch_raises_ex_instrs_raise_ex[OF this]
    have no_fetch_ex: "\<not>fetch_raises_ex ISA tf"
      using Suc.prems \<open>t = tf @ t'\<close>
      by auto
    have ta': "fetch_assms tf"
      using Bind \<open>instrs_assms (Suc n) t\<close>
      by (auto simp: Run_hasTrace[THEN hasTrace_consumesTrace])
    have fetch_mono: "reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s'' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s"
      using tf s'' Bind Suc.prems ta'
      by (intro reachable_caps_plus_fetch_trace_intradomain_monotonicity)
         (auto simp: s_invariant_append fetch_raises_ex_instrs_raise_ex)
    then have fetch_cap_inv: "\<forall>c \<in> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s''. is_tagged_method CC c \<longrightarrow> cap_invariant c"
      using Suc.prems
      by auto
    have inv': "s_invariant_holds (addr_trans_invariant_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) False s'') t' s''"
      using Suc.prems no_fetch_ex ta' fetch_mono s''
      using hasTrace_fetch_cheri_axioms[OF tf, where n = "length tf" and C' = "initial_caps \<union> invoked_instrs_caps (Suc n) (tf @ t')" and s = s]
      unfolding \<open>t = tf @ t'\<close>
      by (elim s_invariant_holds_addr_trans_append_right; auto simp: Un_commute)
    from \<open>(\<lbrakk>instr\<rbrakk> \<then> fetch_execute_loop ISA n, t', m') \<in> Traces\<close>
    have "reachable_caps s' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s''"
    proof (cases rule: bind_Traces_cases)
      case (Left m'')
      then have *: "hasTrace t' \<lbrakk>instr\<rbrakk>"
        using m'
        by (auto elim!: final_bind_cases) (auto simp: hasTrace_iff_Traces_final final_def)
      have ta'': "instr_assms instr t'"
        using Bind \<open>instrs_assms (Suc n) t\<close> hasTrace_consumesTrace[where t' = "[]", OF *]
        by (auto simp: Run_hasTrace[THEN hasTrace_consumesTrace])
      have inv'': "s_invariant_holds (addr_trans_invariant_plus ({} \<union> initial_caps \<union> invoked_instr_caps instr t') False s'') t' s''"
        using inv' \<open>t = tf @ t'\<close>
        using instrs_invoke_caps_Suc[OF \<open>Run (instr_fetch ISA) tf instr\<close> *, where t' = "[]"]
        using instrs_invoke_indirect_caps_Suc[OF \<open>Run (instr_fetch ISA) tf instr\<close> *, where t' = "[]"]
        by (elim s_invariant_holds_weaken addr_trans_invariant_plus_antimono) auto
      have "reachable_caps_plus {} s' \<subseteq> reachable_caps_plus ({} \<union> initial_caps \<union> invoked_instr_caps instr t') s''"
        using * tf t' s'' Bind Suc.prems inv'' ta'' fetch_cap_inv
        using instrs_raise_ex_Suc[OF \<open>Run (instr_fetch ISA) tf instr\<close> *, where t' = "[]"]
        by (intro reachable_caps_plus_instr_trace_intradomain_monotonicity)
           (auto simp add: runTrace_iff_Traces)
      also have "\<dots> \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s''"
        using invoked_instrs_caps_Suc[of tf instr t' n "[]"] Bind *
        by (intro reachable_caps_plus_mono) auto
      finally show ?thesis
        by simp
    next
      case (Bind ti am t'')
      obtain s''' where s''': "s_run_trace ti s'' = Some s'''" and t'': "s_run_trace t'' s''' = Some s'"
        using Bind t'
        by (auto elim: runTraceS_appendE)
      have ti: "hasTrace ti \<lbrakk>instr\<rbrakk>"
        using Bind
        by (auto simp: hasTrace_iff_Traces_final final_def)
      have ta'': "instr_assms instr ti" "instrs_assms n t''"
        using Bind \<open>Run (instr_fetch ISA) tf instr\<close> \<open>t = tf @ t'\<close> \<open>instrs_assms (Suc n) t\<close>
        by (auto simp: Run_hasTrace[THEN hasTrace_consumesTrace])
      have no_exception': "\<not>fetch_raises_ex ISA tf" "\<not>instr_raises_ex ISA instr ti"
        and no_exception'': "\<not>instrs_raise_ex ISA n t''"
        using ti tf Suc.prems Bind \<open>t = tf @ t'\<close>
        using \<open>Run (instr_fetch ISA) tf instr\<close>
        by (auto simp: runTrace_iff_Traces instrs_raise_ex_Suc)
      have inv_caps: "invoked_instrs_caps (Suc n) t = invoked_instrs_caps n t'' \<union> invoked_instr_caps instr ti"
        using invoked_instrs_caps_Suc[OF \<open>Run (instr_fetch ISA) tf instr\<close> ti]
        unfolding \<open>t = tf @ t'\<close> \<open>t' = ti @ t''\<close>
        by auto
      have instr_mono: "reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t'') s''' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps (Suc n) t) s''"
        using ti s''' no_exception' inv' ta'' fetch_cap_inv
        using inv'[unfolded \<open>t' = ti @ t''\<close> inv_caps, THEN s_invariant_holds_addr_trans_append_left]
        unfolding inv_caps
        by (intro reachable_caps_plus_instr_trace_intradomain_monotonicity, blast+)
      then have instr_cap_inv: "\<forall>c \<in> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t'') s'''. is_tagged_method CC c \<longrightarrow> cap_invariant c"
        using fetch_cap_inv
        by auto
      have inv'': "s_invariant_holds (addr_trans_invariant_plus (initial_caps \<union> invoked_instrs_caps n t'') False s''') t'' s'''"
        using inv' s''' Bind ta'' no_exception' instr_mono fetch_cap_inv
        using hasTrace_instr_cheri_axioms[OF ti fetch_cap_inv, where n = "length ti"]
        unfolding \<open>t' = ti @ t''\<close>
        by (elim s_invariant_holds_addr_trans_append_right) (auto intro: instr_cheri_axioms)
      have "reachable_caps s' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t'') s'''"
        using Bind m' t'' inv'' ta'' no_exception'' instr_cap_inv
        by (intro Suc.IH) (auto simp: hasTrace_iff_Traces_final final_def)
      with instr_mono show ?thesis
        by auto
    qed
    with fetch_mono show ?thesis
      by auto
  qed
qed

lemma reachable_caps_instrs_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (fetch_execute_loop ISA n)"
    and ci: "\<forall>c \<in> reachable_caps s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and ta: "instrs_assms n t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instrs_raise_ex ISA n t"
    and invoked_caps_reachable: "invoked_instrs_caps n t \<subseteq> reachable_caps s"
    and initial_caps_reachable: "initial_caps \<subseteq> reachable_caps s"
    and addr_trans_inv: "s_invariant_holds (addr_trans_invariant False s) t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof -
  have *: "initial_caps \<union> invoked_instrs_caps n t \<subseteq> reachable_caps s"
    using invoked_caps_reachable initial_caps_reachable
    by simp
  note [simp] = reachable_caps_plus_subset_eq[OF this] addr_trans_invariant_plus_subset_reachable_caps_eq[OF this]
  from assms have "reachable_caps s' \<subseteq> reachable_caps_plus (initial_caps \<union> invoked_instrs_caps n t) s"
    by (intro reachable_caps_plus_instrs_trace_intradomain_monotonicity) auto
  then show ?thesis
    by simp
qed

end

end
