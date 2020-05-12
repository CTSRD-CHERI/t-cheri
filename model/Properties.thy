theory Properties
imports Cheri_axioms_lemmas Sail.Sail2_state_lemmas
begin

locale CHERI_ISA = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes fetch_assms :: "'regval trace \<Rightarrow> bool" and instr_assms :: "'regval trace \<Rightarrow> bool"
  assumes instr_cheri_axioms: "\<And>t instr. hasTrace t \<lbrakk>instr\<rbrakk> \<Longrightarrow> instr_assms t \<Longrightarrow> cheri_axioms CC ISA False (instr_raises_ex ISA instr t) (invokes_caps ISA instr t) t"
    and fetch_cheri_axioms: "\<And>t. hasTrace t (instr_fetch ISA) \<Longrightarrow> fetch_assms t \<Longrightarrow> cheri_axioms CC ISA True (fetch_raises_ex ISA t) False t"
    and instr_assms_appendE: "\<And>t t' instr. instr_assms (t @ t') \<Longrightarrow> Run \<lbrakk>instr\<rbrakk> t () \<Longrightarrow> instr_assms t \<and> fetch_assms t'"
    and fetch_assms_appendE: "\<And>t t' instr. fetch_assms (t @ t') \<Longrightarrow> Run (instr_fetch ISA) t instr \<Longrightarrow> fetch_assms t \<and> instr_assms t'"

locale Register_Accessors =
  fixes read_regval :: "register_name \<Rightarrow> 'regs \<Rightarrow> 'regval option"
    and write_regval :: "register_name \<Rightarrow> 'regval \<Rightarrow> 'regs \<Rightarrow> 'regs option"
begin

abbreviation "s_emit_event e s \<equiv> emitEventS (read_regval, write_regval) e s"
abbreviation "s_run_trace t s \<equiv> runTraceS (read_regval, write_regval) t s"
abbreviation "s_allows_trace t s \<equiv> \<exists>s'. s_run_trace t s = Some s'"

end

locale CHERI_ISA_State = CHERI_ISA CC ISA + Register_Accessors read_regval write_regval
  for ISA :: "('cap, 'regval, 'instr, 'e) isa"
  and CC :: "'cap Capability_class"
  and read_regval :: "register_name \<Rightarrow> 'regs \<Rightarrow> 'regval option"
  and write_regval :: "register_name \<Rightarrow> 'regval \<Rightarrow> 'regs \<Rightarrow> 'regs option" +
  (* State versions of ISA model parameters *)
  fixes s_translation_tables :: "'regs sequential_state \<Rightarrow> nat set"
    and s_translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> 'regs sequential_state \<Rightarrow> nat option"
  assumes read_absorb_write: "\<And>r v s s'. write_regval r v s = Some s' \<Longrightarrow> read_regval r s' = Some v"
    and read_ignore_write: "\<And>r r' v s s'. write_regval r v s = Some s' \<Longrightarrow> r' \<noteq> r \<Longrightarrow> read_regval r' s' = read_regval r' s"
    and translation_tables_sound: "\<And>t s. s_allows_trace t s \<Longrightarrow> translation_tables ISA t \<subseteq> s_translation_tables s"
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

inductive_set reachable_caps :: "'regs sequential_state \<Rightarrow> 'cap set" for s :: "'regs sequential_state" where
  Reg: "\<lbrakk>c \<in> get_reg_caps r s; r \<notin> privileged_regs ISA; is_tagged_method CC c\<rbrakk> \<Longrightarrow> c \<in> reachable_caps s"
| SysReg:
    "\<lbrakk>c \<in> get_reg_caps r s; r \<in> privileged_regs ISA; c' \<in> reachable_caps s;
      permit_system_access (get_perms_method CC c'); \<not>is_sealed_method CC c';
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps s"
| Mem:
    "\<lbrakk>get_aligned_mem_cap addr (tag_granule ISA) s = Some c;
      s_translate_address vaddr Load s = Some addr;
      c' \<in> reachable_caps s; is_tagged_method CC c'; \<not>is_sealed_method CC c';
      set (address_range vaddr (tag_granule ISA)) \<subseteq> get_mem_region_method CC c';
      permit_load_capability (get_perms_method CC c');
      is_tagged_method CC c\<rbrakk>
     \<Longrightarrow> c \<in> reachable_caps s"
| Restrict: "\<lbrakk>c \<in> reachable_caps s; leq_cap CC c' c\<rbrakk> \<Longrightarrow> c' \<in> reachable_caps s"
| Seal:
    "\<lbrakk>c' \<in> reachable_caps s; c'' \<in> reachable_caps s; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; \<not>is_sealed_method CC c'; permit_seal (get_perms_method CC c'')\<rbrakk> \<Longrightarrow>
     seal CC c' (get_cursor_method CC c'') \<in> reachable_caps s"
| Unseal:
    "\<lbrakk>c' \<in> reachable_caps s; c'' \<in> reachable_caps s; is_tagged_method CC c'; is_tagged_method CC c'';
      \<not>is_sealed_method CC c''; is_sealed_method CC c'; permit_unseal (get_perms_method CC c'');
      get_obj_type_method CC c' = get_cursor_method CC c''\<rbrakk> \<Longrightarrow>
     unseal CC c' (get_global CC c'') \<in> reachable_caps s"

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

lemma derivable_reachable_caps_idem[simp]: "derivable (reachable_caps s) = reachable_caps s"
  using derivable_subseteq_reachableI[of "reachable_caps s" s] derivable_refl
  by auto

lemma runTraceS_rev_induct[consumes 1, case_names Init Step]:
  assumes "s_run_trace t s = Some s'"
    and Init: "P [] s"
    and Step: "\<And>t e s'' s'. s_run_trace t s = Some s'' \<Longrightarrow> s_emit_event e s'' = Some s' \<Longrightarrow> P t s'' \<Longrightarrow> P (t @ [e]) s'"
  shows "P t s'"
  using assms
  by (induction t arbitrary: s' rule: rev_induct)
     (auto elim: runTraceS_appendE runTraceS_ConsE simp: bind_eq_Some_conv)

lemma get_reg_val_s_run_trace_cases:
  assumes v: "get_reg_val r s' = Some v" and c: "c \<in> caps_of_regval ISA v"
    and s': "s_run_trace t s = Some s'"
  obtains (Init) "get_reg_val r s = Some v"
  | (Update) j v' where "t ! j = E_write_reg r v'" and "c \<in> caps_of_regval ISA v'" and "j < length t"
proof (use s' v c in \<open>induction rule: runTraceS_rev_induct\<close>)
  case (Step t e s'' s')
  note Init = Step(4)
  note Update = Step(5)
  note c = \<open>c \<in> caps_of_regval ISA v\<close>
  show ?case
  proof cases
    assume v_s'': "get_reg_val r s'' = Some v"
    show ?thesis
    proof (rule Step.IH[OF _ _ v_s'' c])
      assume "get_reg_val r s = Some v"
      then show thesis by (intro Init)
    next
      fix j v'
      assume "t ! j = E_write_reg r v'" and "c \<in> caps_of_regval ISA v'" and "j < length t"
      then show thesis by (intro Update[of j v']) (auto simp: nth_append_left)
    qed
  next
    assume v_s'': "get_reg_val r s'' \<noteq> Some v"
    note e = \<open>s_emit_event e s'' = Some s'\<close>
    note v_s' = \<open>get_reg_val r s' = Some v\<close>
    from e v_s' v_s'' have "e = E_write_reg r v"
    proof (cases rule: emitEventS_update_cases)
      case (Write_reg r' v' rs')
      then show ?thesis
        using v_s' v_s''
        by (cases "r' = r") (auto simp: read_ignore_write read_absorb_write)
    qed (auto simp: put_mem_bytes_def Let_def)
    then show thesis using c by (auto intro: Update[of "length t" v])
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
  shows "available_caps CC ISA j t \<subseteq> available_caps CC ISA i t"
proof -
  have "available_caps CC ISA j t \<subseteq> available_caps CC ISA (Suc (j + k)) t" for k
    by (induction k) (auto simp: available_caps_Suc image_iff subset_iff)
  then show ?thesis using assms less_iff_Suc_add[of j i] by blast
qed

lemma reads_reg_cap_non_privileged_accessible[intro]:
  assumes "c \<in> caps_of_regval ISA v" and "t ! j = E_read_reg r v"
    and "\<not>cap_reg_written_before_idx CC ISA j r t"
    and "r \<notin> privileged_regs ISA"
    and "is_tagged_method CC c"
    and "j < i"
    and "j < length t"
  shows "c \<in> available_caps CC ISA i t"
proof -
  from assms have c: "c \<in> available_caps CC ISA (Suc j) t"
    by (auto simp: bind_eq_Some_conv image_iff available_caps.simps)
  consider "i = Suc j" | "Suc j < i" using \<open>j < i\<close>
    by (cases "i = Suc j") auto
  then show "c \<in> available_caps CC ISA i t"
    using c available_caps_mono[of "Suc j" i t]
    by cases auto
qed

lemma system_access_permitted_at_idx_available_caps:
  assumes "system_access_permitted_before_idx CC ISA i t"
  obtains c where "c \<in> available_caps CC ISA i t" and "is_tagged_method CC c"
    and "\<not>is_sealed_method CC c" and "permit_system_access (get_perms_method CC c)"
  using assms
  by (auto simp: system_access_permitted_before_idx_def; blast)

lemma writes_reg_cap_nth_provenance[consumes 5]:
  assumes "t ! i = E_write_reg r v" and "c \<in> caps_of_regval ISA v"
    and "cheri_axioms CC ISA is_fetch has_ex inv_caps t"
    and "i < length t"
    and tagged: "is_tagged_method CC c"
  obtains (Accessible) "c \<in> derivable (available_caps CC ISA i t)"
  | (Exception) v' r' j where "c \<in> exception_targets ISA {v. \<exists>r j. j < i \<and> j < length t \<and> t ! j = E_read_reg r v \<and> r \<in> KCC ISA}" (* "leq_cap CC c c'"*)
    (*and "t ! j = E_read_reg r' v'" and "j < i"*) (*and "c' \<in> caps_of_regval ISA v'"*)
    (*and "r' \<in> KCC ISA"*) and "r \<in> PCC ISA" and "has_ex"
  | (CCall) cc cd c' where "inv_caps" (*"(cc, cd) \<in> inv_caps"*) and "invokable CC cc cd"
    and "cc \<in> derivable (available_caps CC ISA i t)"
    and "cd \<in> derivable (available_caps CC ISA i t)"
    and "(r \<in> PCC ISA \<and> leq_cap CC c (unseal CC cc True)) \<or>
         (r \<in> IDC ISA \<and> leq_cap CC c (unseal CC cd True))"
  using assms
  unfolding cheri_axioms_def store_cap_reg_axiom_def writes_reg_caps_at_idx_def cap_derivable_iff_derivable
  by (elim impE conjE allE[where x = i] allE[where x = c])
     (auto simp: eq_commute[where b = "t ! j" for t j])

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
    and axioms: "cheri_axioms CC ISA is_fetch has_ex inv_caps t"
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

definition no_caps_in_translation_tables :: "'regs sequential_state \<Rightarrow> bool" where
  "no_caps_in_translation_tables s \<equiv>
     \<forall>addr sz c. get_mem_cap addr sz s = Some c \<and> is_tagged_method CC c \<longrightarrow>
                 addr \<notin> s_translation_tables s"

lemma derivable_available_caps_subseteq_reachable_caps:
  assumes axioms: "cheri_axioms CC ISA is_fetch has_ex inv_caps t"
    and t: "s_run_trace t s = Some s'"
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
  shows "derivable (available_caps CC ISA i t) \<subseteq> reachable_caps s"
proof (induction i rule: less_induct)
  case (less i)
  show ?case proof
    fix c
    assume "c \<in> derivable (available_caps CC ISA i t)"
    then show "c \<in> reachable_caps s"
    proof induction
      fix c
      assume "c \<in> available_caps CC ISA i t"
      then show "c \<in> reachable_caps s"
      proof (cases rule: available_caps_cases)
        case (Reg r v j)
        from Reg(1-4) t
        show ?thesis
        proof (cases rule: reads_reg_cap_at_idx_provenance)
          case Initial
          show ?thesis
          proof cases
            assume r: "r \<in> privileged_regs ISA"
            then obtain c' where c': "c' \<in> reachable_caps s" and "is_tagged_method CC c'"
              and "\<not>is_sealed_method CC c'" and p: "permit_system_access (get_perms_method CC c')"
              using Reg less.IH[OF \<open>j < i\<close>] derivable_refl[of "available_caps CC ISA j t"]
              by (auto elim!: system_access_permitted_at_idx_available_caps)
            then show ?thesis
              using Reg
              by (auto intro: reachable_caps.SysReg[OF Initial r c'])
          next
            assume "r \<notin> privileged_regs ISA"
            then show ?thesis using Initial Reg by (auto intro: reachable_caps.Reg)
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
        have addr: "paddr \<notin> translation_tables ISA (take j t)"
        proof
          assume paddr_j: "paddr \<in> translation_tables ISA (take j t)"
          then have "paddr \<in> s_translation_tables s"
            using translation_tables_sound[of "take j t" s] t \<open>j < length t\<close>
            by (auto elim: runTraceS_nth_split)
          moreover have "paddr \<notin> s_translation_tables s"
          proof -
            obtain s''
              where s'': "s_run_trace (take j t) s = Some s''"
                and c_s'': "get_mem_cap paddr sz s'' = Some c"
              using t \<open>j < length t\<close> read bytes \<open>is_tagged_method CC c\<close>
              by (cases rule: runTraceS_nth_split; cases "t ! j")
                 (auto simp: bind_eq_Some_conv reads_mem_cap_def split: if_splits)
            moreover have "no_caps_in_translation_tables s''"
              using no_caps_in_translation_tables s''
              using s_invariant_takeI[of no_caps_in_translation_tables t s j]
              using s_invariant_run_trace_eq[of no_caps_in_translation_tables "take j t" s s'']
              by auto
            moreover have "s_translation_tables s'' = s_translation_tables s"
              using translation_table_addrs_invariant s''
              by (intro s_invariant_run_trace_eq) (auto intro: s_invariant_takeI)
            ultimately show ?thesis
              using \<open>is_tagged_method CC c\<close>
              by (fastforce simp: no_caps_in_translation_tables_def bind_eq_Some_conv)
          qed
          ultimately show False by blast
        qed
        then obtain vaddr c'
          where vaddr: "translate_address ISA vaddr Load (take j t) = Some paddr"
            and c': "c' \<in> derivable (available_caps CC ISA j t)"
                    "is_tagged_method CC c'" "\<not>is_sealed_method CC c'"
                    "set (address_range vaddr sz) \<subseteq> get_mem_region_method CC c'"
                    "permit_load (get_perms_method CC c')"
                    "permit_load_capability (get_perms_method CC c')"
            and sz: "sz = tag_granule ISA"
            and aligned: "address_tag_aligned ISA paddr"
          using read t axioms \<open>j < length t\<close> \<open>is_tagged_method CC c\<close>
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
            by (intro reachable_caps.Mem[of paddr s c vaddr c'])
               (auto simp: bind_eq_Some_conv translate_address_tag_aligned_iff permits_cap_load_def)
        next
          case (Update k wk bytes' r)
          then show ?thesis
            using axioms \<open>is_tagged_method CC c\<close> \<open>j < length t\<close> \<open>j < i\<close> less.IH[of k]
            unfolding cheri_axioms_def store_cap_mem_axiom_def
            by (auto simp: writes_mem_cap_at_idx_def writes_mem_cap_Some_iff bind_eq_Some_conv cap_derivable_iff_derivable)
        qed
      qed
    qed (auto intro: reachable_caps.intros)
  qed
qed

lemma put_regval_get_mem_cap:
  assumes s': "put_reg_val r v s = Some s'"
    and "s_translate_address addr acctype s' = s_translate_address addr acctype s"
  shows "get_mem_cap addr sz s' = get_mem_cap addr sz s"
  using assms by (auto cong: bind_option_cong simp: get_mem_bytes_def)

definition system_access_reachable :: "'regs sequential_state \<Rightarrow> bool" where
  "system_access_reachable s \<equiv> \<exists>c \<in> reachable_caps s.
     permit_system_access (get_perms_method CC c) \<and> \<not>is_sealed_method CC c"

lemma get_reg_cap_intra_domain_trace_reachable:
  assumes r: "c \<in> get_reg_caps r s'"
    (*and t: "hasTrace t (instr_sem ISA instr)"*) and s': "s_run_trace t s = Some s'"
    and axioms: "cheri_axioms CC ISA is_fetch False False t"
    (*and no_exception: "\<not>hasException t (instr_sem ISA instr)"
    and no_ccall: "invoked_caps ISA instr t = {}"*)
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
    and tag: "is_tagged_method CC c"
    and priv: "r \<in> privileged_regs ISA \<longrightarrow> system_access_reachable s"
  shows "c \<in> reachable_caps s"
proof -
  from r obtain v where v: "get_reg_val r s' = Some v" and c: "c \<in> caps_of_regval ISA v"
    by (auto simp: bind_eq_Some_conv split: option.splits)
  from v c s' show "c \<in> reachable_caps s"
  proof (cases rule: get_reg_val_s_run_trace_cases)
    case Init
    show ?thesis
    proof cases
      assume r: "r \<in> privileged_regs ISA"
      with priv obtain c' where c': "c' \<in> reachable_caps s"
        and "permit_system_access (get_perms_method CC c')" and "\<not>is_sealed_method CC c'"
        by (auto simp: system_access_reachable_def)
      then show ?thesis using Init c tag by (intro reachable_caps.SysReg[OF _ r c']) auto
    next
      assume "r \<notin> privileged_regs ISA"
      then show ?thesis using Init c tag by (intro reachable_caps.Reg) auto
    qed
  next
    case (Update j v')
    then have *: "c \<in> writes_reg_caps CC (caps_of_regval ISA) (t ! j)"
      and "writes_to_reg (t ! j) = Some r"
      using c tag by auto
    then have "c \<in> derivable (available_caps CC ISA j t)"
      using axioms tag \<open>j < length t\<close>
      unfolding cheri_axioms_def store_cap_reg_axiom_def
      by (fastforce simp: cap_derivable_iff_derivable)
    moreover have "derivable (available_caps CC ISA j t) \<subseteq> reachable_caps s"
      using axioms s' translation_table_addrs_invariant no_caps_in_translation_tables
      by (intro derivable_available_caps_subseteq_reachable_caps)
    ultimately show ?thesis by auto
  qed
qed

lemma reachable_caps_trace_intradomain_monotonicity:
  assumes axioms: "cheri_axioms CC ISA is_fetch False False t"
    and s': "s_run_trace t s = Some s'"
    and addr_trans_inv: "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t s"
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof
  fix c
  assume "c \<in> reachable_caps s'"
  then show "c \<in> reachable_caps s"
  proof induction
    case (Reg r c)
    then show ?case
      using axioms s' translation_table_addrs_invariant no_caps_in_translation_tables
      by (intro get_reg_cap_intra_domain_trace_reachable) auto
  next
    case (SysReg r c c')
    then show ?case
      using axioms s' translation_table_addrs_invariant no_caps_in_translation_tables
      by (intro get_reg_cap_intra_domain_trace_reachable) (auto simp: system_access_reachable_def)
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
        using s_invariant_run_trace_eq[OF addr_trans_inv s']
        by meson
      then show ?thesis
        using Initial Mem
        by (intro reachable_caps.Mem[of addr s c vaddr c']) (auto split: if_splits)
    next
      case (Update k wk bytes r)
      have "derivable (available_caps CC ISA k t) \<subseteq> reachable_caps s"
        using assms axioms
        by (intro derivable_available_caps_subseteq_reachable_caps)
      then show ?thesis
        using Update \<open>is_tagged_method CC c\<close> axioms
        unfolding cheri_axioms_def store_cap_mem_axiom_def cap_derivable_iff_derivable
        by (auto simp: writes_mem_cap_at_idx_def writes_mem_cap_Some_iff)
    qed
  qed (auto intro: reachable_caps.intros)
qed

lemma reachable_caps_instr_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_sem ISA instr)"
    and ta: "instr_assms t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instr_raises_ex ISA instr t"
    and no_ccall: "\<not>invokes_caps ISA instr t"
    and addr_trans_inv: "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t s"
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
  using assms instr_cheri_axioms[OF t ta]
  by (intro reachable_caps_trace_intradomain_monotonicity) auto

lemma reachable_caps_fetch_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (instr_fetch ISA)"
    and ta: "fetch_assms t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>fetch_raises_ex ISA t"
    and addr_trans_inv: "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t s"
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
  using assms fetch_cheri_axioms[OF t ta]
  by (intro reachable_caps_trace_intradomain_monotonicity) auto

end

text \<open>Multi-instruction sequences\<close>

fun fetch_execute_loop :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> ('regval, unit, 'e) monad" where
  "fetch_execute_loop ISA (Suc bound) = (instr_fetch ISA \<bind> instr_sem ISA) \<then> fetch_execute_loop ISA bound"
| "fetch_execute_loop ISA 0 = return ()"

fun instrs_raise_ex :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "instrs_raise_ex ISA (Suc bound) t =
    (\<exists>tf t'. t = tf @ t' \<and> hasTrace tf (instr_fetch ISA) \<and>
             (fetch_raises_ex ISA tf \<or>
              (\<exists>instr ti t''. t' = ti @ t'' \<and>
                 runTrace tf (instr_fetch ISA) = Some (Done instr) \<and>
                 hasTrace ti (instr_sem ISA instr) \<and>
                 (instr_raises_ex ISA instr ti \<or>
                  instrs_raise_ex ISA bound t''))))"
| "instrs_raise_ex ISA 0 t = False"

fun instrs_invoke_caps :: "('cap, 'regval, 'instr, 'e) isa \<Rightarrow> nat \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "instrs_invoke_caps ISA (Suc bound) t =
    (\<exists>tf t'. t = tf @ t' \<and> hasTrace tf (instr_fetch ISA) \<and>
          (\<exists>instr ti t''. t' = ti @ t'' \<and>
             runTrace tf (instr_fetch ISA) = Some (Done instr) \<and>
             hasTrace ti (instr_sem ISA instr) \<and>
             (invokes_caps ISA instr ti \<or>
              instrs_invoke_caps ISA bound t'')))"
| "instrs_invoke_caps ISA 0 t = False"

context CHERI_ISA_State
begin

lemma reachable_caps_instrs_trace_intradomain_monotonicity:
  assumes t: "hasTrace t (fetch_execute_loop ISA n)"
    and ta: "fetch_assms t"
    and s': "s_run_trace t s = Some s'"
    and no_exception: "\<not>instrs_raise_ex ISA n t"
    and no_ccall: "\<not>instrs_invoke_caps ISA n t"
    and addr_trans_inv: "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t s"
    and translation_table_addrs_invariant: "s_invariant s_translation_tables t s"
    and no_caps_in_translation_tables: "s_invariant_holds no_caps_in_translation_tables t s"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof (use assms in \<open>induction n arbitrary: s t\<close>)
  case 0
  then show ?case by (auto simp: return_def hasTrace_iff_Traces_final)
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
    then show ?thesis
      using Suc.prems
      by (intro reachable_caps_fetch_trace_intradomain_monotonicity) auto
  next
    case (Bind tf instr t')
    obtain s'' where s'': "s_run_trace tf s = Some s''" and t': "s_run_trace t' s'' = Some s'"
      using Bind Suc
      by (auto elim: runTraceS_appendE)
    have tf: "hasTrace tf (instr_fetch ISA)"
      using Bind
      by (auto simp: hasTrace_iff_Traces_final final_def)
    have invs':
      "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t' s''"
      "s_invariant s_translation_tables t' s''"
      "s_invariant_holds no_caps_in_translation_tables t' s''"
      using tf s'' Bind Suc.prems
      using s_invariant_run_trace_eq[of no_caps_in_translation_tables tf s s'']
      by (auto simp: s_invariant_append)
    have ta': "fetch_assms tf" "instr_assms t'"
      using Bind Suc.prems fetch_assms_appendE
      by auto
    from \<open>(\<lbrakk>instr\<rbrakk> \<then> fetch_execute_loop ISA n, t', m') \<in> Traces\<close>
    have "reachable_caps s' \<subseteq> reachable_caps s''"
    proof (cases rule: bind_Traces_cases)
      case (Left m'')
      then have "hasTrace t' \<lbrakk>instr\<rbrakk>"
        using m'
        by (auto elim!: final_bind_cases) (auto simp: hasTrace_iff_Traces_final final_def)
      then show ?thesis
        using tf t' s'' Bind Suc.prems invs' ta'
        by (intro reachable_caps_instr_trace_intradomain_monotonicity)
           (auto simp: runTrace_iff_Traces)
    next
      case (Bind ti am t'')
      obtain s''' where s''': "s_run_trace ti s'' = Some s'''" and t'': "s_run_trace t'' s''' = Some s'"
        using Bind t'
        by (auto elim: runTraceS_appendE)
      have ti: "hasTrace ti \<lbrakk>instr\<rbrakk>"
        using Bind
        by (auto simp: hasTrace_iff_Traces_final final_def)
      have invs'':
        "s_invariant (\<lambda>s' addr load. s_translate_address addr load s') t'' s'''"
        "s_invariant s_translation_tables t'' s'''"
        "s_invariant_holds no_caps_in_translation_tables t'' s'''"
        using invs' s''' Bind
        using s_invariant_run_trace_eq[of no_caps_in_translation_tables ti s'' s''']
        by (auto simp: s_invariant_append)
      have ta'': "instr_assms ti" "fetch_assms t''"
        using Bind ta' instr_assms_appendE
        by auto
      have no_exception': "\<not>fetch_raises_ex ISA tf" "\<not>instr_raises_ex ISA instr ti"
        and no_ccall': "\<not>invokes_caps ISA instr ti"
        and no_exception'': "\<not>instrs_raise_ex ISA n t''"
        and no_ccall'': "\<not>instrs_invoke_caps ISA n t''"
        using ti tf Suc.prems Bind \<open>t = tf @ t'\<close>
        using \<open>Run (instr_fetch ISA) tf instr\<close>
        by (auto simp: runTrace_iff_Traces)
      then have "reachable_caps s' \<subseteq> reachable_caps s'''"
        using Bind m' t'' invs'' ta''
        by (intro Suc.IH) (auto simp: hasTrace_iff_Traces_final final_def)
      also have "reachable_caps s''' \<subseteq> reachable_caps s''"
        using ti s''' no_exception' no_ccall' invs' \<open>t' = ti @ t''\<close> ta''
        by (intro reachable_caps_instr_trace_intradomain_monotonicity)
           (auto simp: s_invariant_append)
      finally show ?thesis .
    qed
    also have "reachable_caps s'' \<subseteq> reachable_caps s"
      using tf s'' Bind Suc.prems ta'
      by (intro reachable_caps_fetch_trace_intradomain_monotonicity)
         (auto simp: s_invariant_append)
    finally show ?thesis .
  qed
qed

end

end
