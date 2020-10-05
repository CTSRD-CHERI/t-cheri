theory Recognising_Automata
imports Cheri_axioms_lemmas Sail.Sail2_state_lemmas Trace_Assumptions
begin

text \<open>For proving that a concrete ISA satisfies the CHERI axioms, we define an automaton for
each axiom that only accepts traces satisfying the axiom.  The state of the automaton keeps track
of relevant information, e.g. the capabilities read so far.

This makes it easy to decompose proofs about complete instruction traces into proofs about parts
of a trace, e.g. corresponding to calls to auxiliary functions.\<close>

locale Deterministic_Automaton =
  fixes enabled :: "'s \<Rightarrow> 'rv event \<Rightarrow> bool"
    and step :: "'s \<Rightarrow> 'rv event \<Rightarrow> 's"
    and initial :: "'s"
    and final :: "'s \<Rightarrow> bool"
begin

fun trace_enabled :: "'s \<Rightarrow> 'rv trace \<Rightarrow> bool" where
  "trace_enabled s [] = True"
| "trace_enabled s (e # t) = (enabled s e \<and> trace_enabled (step s e) t)"

abbreviation run :: "'s \<Rightarrow> 'rv trace \<Rightarrow> 's" where "run s t \<equiv> foldl step s t"

definition accepts_from :: "'s \<Rightarrow> 'rv trace \<Rightarrow> bool" where
  "accepts_from s t \<equiv> trace_enabled s t \<and> final (run s t)"

abbreviation "accepts \<equiv> accepts_from initial"

lemma trace_enabled_append_iff: "trace_enabled s (t @ t') \<longleftrightarrow> trace_enabled s t \<and> trace_enabled (run s t) t'"
  by (induction t arbitrary: s) auto

lemma accepts_from_append_iff: "accepts_from s (t @ t') \<longleftrightarrow> trace_enabled s t \<and> accepts_from (run s t) t'"
  by (auto simp: accepts_from_def trace_enabled_append_iff)

lemma accepts_from_Cons[simp]: "accepts_from s (e # t) \<longleftrightarrow> enabled s e \<and> accepts_from (step s e) t"
  by (auto simp: accepts_from_def)

lemma accepts_from_id_take_nth_drop:
  assumes "i < length t"
  shows "accepts_from s t = accepts_from s (take i t @ t ! i # drop (Suc i) t)"
  using assms
  by (auto simp: id_take_nth_drop[symmetric])

lemma accepts_from_trace_enabledI:
  assumes "accepts_from s t"
  shows "trace_enabled s t"
  using assms
  by (auto simp: accepts_from_def)

lemma accepts_from_trace_enabled_takeI:
  assumes "accepts_from s t"
  shows "trace_enabled s (take i t)"
  using assms
  by (cases "i < length t") 
     (auto simp: accepts_from_id_take_nth_drop accepts_from_append_iff intro: accepts_from_trace_enabledI)

lemma accepts_from_nth_enabledI:
  assumes "accepts_from s t"
    and "i < length t"
  shows "enabled (run s (take i t)) (t ! i)"
  using assms
  by (auto simp: accepts_from_id_take_nth_drop accepts_from_append_iff)

lemma accepts_from_iff_all_enabled_final:
  "accepts_from s t \<longleftrightarrow> (\<forall>i < length t. enabled (run s (take i t)) (t ! i)) \<and> final (run s t)"
  by (induction t arbitrary: s)
     (auto simp: accepts_from_def nth_Cons split: nat.splits)

lemma trace_enabled_acceptI:
  assumes "trace_enabled s t" and "final (run s t)"
  shows "accepts_from s t"
  using assms
  by (auto simp: accepts_from_def)

named_theorems trace_simp
named_theorems trace_elim

lemma Nil_trace_enabled[trace_elim]:
  assumes "t = []"
  shows "trace_enabled s t"
  using assms
  by auto

lemma bind_TracesE:
  assumes "(m \<bind> f, t, m') \<in> Traces"
    and "\<And>tm tf m''. (m, tm, m'') \<in> Traces \<Longrightarrow> t = tm @ tf \<Longrightarrow> P tm"
    and "\<And>tm am tf. (f am, tf, m') \<in> Traces \<Longrightarrow> Run m tm am \<Longrightarrow> t = tm @ tf \<Longrightarrow> P tm \<Longrightarrow> P (tm @ tf)"
  shows "P t"
proof (use assms in \<open>cases rule: bind_Traces_cases\<close>)
  case (Left m'')
  then show ?thesis using assms(2)[where tm = t and tf = "[]"] by auto
next
  case (Bind tm am tf)
  then show ?thesis using assms(2) assms(3) by auto
qed

lemma Run_bind_trace_enabled[trace_elim]:
  assumes "Run (m \<bind> f) t a"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> Run (f am) tf a \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
  using assms
  by (elim Run_bindE) (auto simp: trace_enabled_append_iff)

lemma Exception_bind_trace_enabled:
  assumes "(m \<bind> f, t, Exception e) \<in> Traces"
    and "(m, t, Exception e) \<in> Traces \<Longrightarrow> trace_enabled s t"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> (f am, tf, Exception e) \<in> Traces \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
proof (use assms in \<open>cases rule: bind_Traces_cases\<close>)
  case (Left m'')
  then consider (Ex) "m'' = Exception e" | (Done) a where "m'' = Done a" and "f a = Exception e"
    by (cases m'') auto
  then show ?thesis
    using \<open>(m, t, m'') \<in> Traces\<close> assms
    by cases auto
next
  case (Bind tm am tf)
  then show ?thesis
    using assms
    by (auto simp: trace_enabled_append_iff)
qed

lemma bind_Traces_trace_enabled[trace_elim]:
  assumes "(m \<bind> f, t, m') \<in> Traces"
    and "\<And>tm tf m''. (m, tm, m'') \<in> Traces \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm am tf. (f am, tf, m') \<in> Traces \<Longrightarrow> Run m tm am \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
  using assms
  by (elim bind_TracesE) (auto simp: trace_enabled_append_iff)

lemma try_catch_trace_enabled[trace_elim]:
  assumes "(try_catch m h, t, m') \<in> Traces"
    and "\<And>n m''. (m, take n t, m'') \<in> Traces \<Longrightarrow> trace_enabled s (take n t)"
    and "\<And>tm ex th. (h ex, th, m') \<in> Traces \<Longrightarrow> (m, tm, Exception ex) \<in> Traces \<Longrightarrow> t = tm @ th \<Longrightarrow> trace_enabled (run s tm) th"
  shows "trace_enabled s t"
proof (use assms in \<open>cases rule: try_catch_Traces_cases\<close>)
  case (NoEx m'')
  then show ?thesis using assms(2)[of "length t" m''] by auto
next
  case (Ex tm ex th)
  then show ?thesis using assms(2)[of "length tm"] assms(3) by (auto simp: trace_enabled_append_iff)
qed

lemma if_Traces_trace_enabled[trace_elim]:
  assumes "(if b then m1 else m2, t, m') \<in> Traces"
    and "b \<Longrightarrow> (m1, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t"
    and "\<not>b \<Longrightarrow> (m2, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t"
  shows "trace_enabled s t"
  using assms by (cases b) auto

lemma let_Traces_trace_enabled[trace_elim]:
  assumes "(let x = y in f x, t, m') \<in> Traces"
    and "(f y, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t"
  shows "trace_enabled s t"
  using assms by auto

lemma case_prod_Traces_trace_enabled[trace_elim]:
  assumes "(case p of (a, b) \<Rightarrow> f a b, t, m') \<in> Traces"
    and "\<And>x y. p = (x, y) \<Longrightarrow> (f x y, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t"
  shows "trace_enabled s t"
  using assms by (cases p) auto

lemma case_option_Traces_trace_enabled[trace_elim]:
  assumes "(case x of Some y \<Rightarrow> f y | None \<Rightarrow> m, t, m') \<in> Traces"
    and "\<And>y. (f y, t, m') \<in> Traces \<Longrightarrow> x = Some y \<Longrightarrow> trace_enabled s t"
    and "(m, t, m') \<in> Traces \<Longrightarrow> x = None \<Longrightarrow> trace_enabled s t"
  shows "trace_enabled s t"
  using assms by (cases x) auto

lemma return_trace_enabled[trace_elim]:
  assumes "(return a, t, m') \<in> Traces"
  shows "trace_enabled s t"
  using assms
  by (auto simp: return_def)

lemma throw_trace_enabled[trace_elim]:
  assumes "(throw e, t, m') \<in> Traces"
  shows "trace_enabled s t"
  using assms
  by (auto simp: throw_def)

lemma early_return_trace_enabled[trace_elim]:
  assumes "(early_return a, t, m') \<in> Traces"
  shows "trace_enabled s t"
  using assms
  by (auto simp: early_return_def elim!: trace_elim)

lemma catch_early_return_trace_enabled[trace_elim]:
  assumes "(catch_early_return m, t, m') \<in> Traces"
    and "\<And>n m''. (m, take n t, m'') \<in> Traces \<Longrightarrow> trace_enabled s (take n t)"
  shows "trace_enabled s t"
  using assms
  by (auto simp: catch_early_return_def elim!: trace_elim split: sum.splits)

lemma liftR_trace_enabled[trace_elim]:
  assumes "(liftR m, t, m') \<in> Traces"
    and "\<And>n m''. (m, take n t, m'') \<in> Traces \<Longrightarrow> trace_enabled s (take n t)"
  shows "trace_enabled s t"
  using assms
  by (auto simp: liftR_def elim!: trace_elim)

lemma foreachM_inv_trace_enabled:
  assumes "(foreachM xs vars body, t, m') \<in> Traces"
    and "\<And>s x vars t m'. (body x vars, t, m') \<in> Traces \<Longrightarrow> P s \<Longrightarrow> x \<in> set xs \<Longrightarrow> trace_enabled s t"
    and "\<And>s x vars t vars'. Run (body x vars) t vars' \<Longrightarrow> P s \<Longrightarrow> x \<in> set xs \<Longrightarrow> P (run s t)"
    and "P s"
  shows "trace_enabled s t"
  using assms
  by (induction xs arbitrary: s t vars) (auto simp: trace_enabled_append_iff elim!: trace_elim)

lemma foreachM_const_trace_enabled[trace_elim]:
  assumes "(foreachM xs vars body, t, m') \<in> Traces"
    and "\<And>x vars t m'. (body x vars, t, m') \<in> Traces \<Longrightarrow> x \<in> set xs \<Longrightarrow> trace_enabled s t"
    and "\<And>x vars t vars'. Run (body x vars) t vars' \<Longrightarrow> x \<in> set xs \<Longrightarrow> run s t = s"
  shows "trace_enabled s t"
  using assms
  by (elim foreachM_inv_trace_enabled[where P = "\<lambda>s'. s' = s"]) auto

lemma Run_and_boolM_trace_enabled[trace_elim]:
  assumes "Run (and_boolM l r) t a"
    and "\<And>tl tr al. t = tl @ tr \<Longrightarrow> Run l tl al \<Longrightarrow> trace_enabled s tl"
    and "\<And>tl tr. t = tl @ tr \<Longrightarrow> Run l tl True \<Longrightarrow> Run r tr a \<Longrightarrow> trace_enabled (run s tl) tr"
  shows "trace_enabled s t"
  using assms
  unfolding and_boolM_def
  by (elim Run_bind_trace_enabled) (auto simp: return_def split: if_splits)

lemma and_boolM_trace_enabled[trace_elim]:
  assumes "(and_boolM m1 m2, t, m') \<in> Traces"
    and "\<And>tm tf m''. (m1, tm, m'') \<in> Traces \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm tf. (m2, tf, m') \<in> Traces \<Longrightarrow> Run m1 tm True \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
  using assms
  by (auto simp: and_boolM_def elim!: trace_elim)

lemma Run_or_boolM_trace_enabled[trace_elim]:
  assumes "Run (or_boolM l r) t a"
    and "\<And>tl tr al. t = tl @ tr \<Longrightarrow> Run l tl al \<Longrightarrow> trace_enabled s tl"
    and "\<And>tl tr. t = tl @ tr \<Longrightarrow> Run l tl False \<Longrightarrow> Run r tr a \<Longrightarrow> trace_enabled (run s tl) tr"
  shows "trace_enabled s t"
  using assms
  unfolding or_boolM_def
  by (elim Run_bind_trace_enabled) (auto simp: return_def split: if_splits)

lemma or_boolM_trace_enabled[trace_elim]:
  assumes "(or_boolM m1 m2, t, m') \<in> Traces"
    and "\<And>tm tf m''. (m1, tm, m'') \<in> Traces \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm tf. (m2, tf, m') \<in> Traces \<Longrightarrow> Run m1 tm False \<Longrightarrow> t = tm @ tf \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
  using assms
  by (auto simp: or_boolM_def elim!: trace_elim)

end

text \<open>An automaton for the axiom that capabilities stored to memory must be derivable from
accessible capabilities\<close>

record ('cap, 'regval) axiom_state =
  accessed_reg_caps :: "'cap set"
  accessed_mem_caps :: "'cap set"
  system_reg_access :: bool
  read_from_KCC :: "'regval set"
  written_regs :: "string set"

definition accessed_caps where
  "accessed_caps use_mem_caps s \<equiv> accessed_reg_caps s \<union> (if use_mem_caps then accessed_mem_caps s else {})"

locale Cap_Axiom_Automaton = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool"
    and use_mem_caps :: bool
begin

definition accessible_regs :: "('cap, 'regval) axiom_state \<Rightarrow> register_name set" where
  "accessible_regs s = {r. (r \<in> PCC ISA \<union> IDC ISA \<longrightarrow> r \<notin> written_regs s) \<and> (r \<in> privileged_regs ISA \<longrightarrow> system_reg_access s)}"

definition axiom_step :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> ('cap, 'regval) axiom_state" where
  "axiom_step s e = \<lparr>accessed_reg_caps = accessed_reg_caps s \<union> accessed_reg_caps_of_ev (accessible_regs s) e,
                     accessed_mem_caps = accessed_mem_caps s \<union> accessed_mem_caps_of_ev e,
                     system_reg_access = system_reg_access s \<or> allows_system_reg_access (accessible_regs s) e,
                     read_from_KCC = read_from_KCC s \<union> {v. \<exists>r \<in> KCC ISA. e = E_read_reg r v},
                     written_regs = written_regs s \<union> {r. \<exists>v c. e = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}\<rparr>"

lemma step_selectors[simp]:
  "accessed_reg_caps (axiom_step s e) = accessed_reg_caps s \<union> accessed_reg_caps_of_ev (accessible_regs s) e"
  "accessed_mem_caps (axiom_step s e) = accessed_mem_caps s \<union> accessed_mem_caps_of_ev e"
  "system_reg_access (axiom_step s e) \<longleftrightarrow> system_reg_access s \<or> allows_system_reg_access (accessible_regs s) e"
  "read_from_KCC (axiom_step s e) = read_from_KCC s \<union> {v. \<exists>r \<in> KCC ISA. e = E_read_reg r v}"
  "written_regs (axiom_step s e) = written_regs s \<union> {r. \<exists>v c. e = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
  by (auto simp: axiom_step_def)

abbreviation "initial \<equiv> \<lparr>accessed_reg_caps = {}, accessed_mem_caps = {}, system_reg_access = False, read_from_KCC = {}, written_regs = {}\<rparr>"

lemma accessible_regs_initial_iff[simp]:
  "r \<in> accessible_regs initial \<longleftrightarrow> r \<notin> privileged_regs ISA"
  by (auto simp: accessible_regs_def)

sublocale Deterministic_Automaton enabled axiom_step initial "\<lambda>_. True" .

lemma cap_reg_written_before_idx_written_regs:
  "cap_reg_written_before_idx CC ISA i r t \<longleftrightarrow> r \<in> written_regs (run initial (take i t))"
proof (induction i)
  case (Suc i)
  then show ?case
    by (cases "i < length t") (auto simp: take_Suc_conv_app_nth)
qed auto

lemma accessible_regs_axiom_step:
  "accessible_regs (axiom_step s e) =
     accessible_regs s \<union>
     (if allows_system_reg_access (accessible_regs s) e then privileged_regs ISA else {}) -
     (written_regs (axiom_step s e) \<inter> (PCC ISA \<union> IDC ISA))"
  by (auto simp: accessible_regs_def)

lemma system_reg_access_run_take_eq[simp]:
  "system_access_permitted_before_idx CC ISA i t \<longleftrightarrow> system_reg_access (run initial (take i t))"
    (is "?sys_reg_access i")
  "accessible_regs_at_idx i t = accessible_regs (run initial (take i t))"
    (is "?accessible_regs i")
proof (induction i)
  case (Suc i)
  show "?accessible_regs (Suc i)"
    by (cases "i < length t")
       (auto simp: Suc.IH accessible_regs_def accessible_regs_at_idx_def
                   cap_reg_written_before_idx_written_regs take_Suc_conv_app_nth)
  show "?sys_reg_access (Suc i)"
    by (cases "i < length t") (auto simp: Suc.IH take_Suc_conv_app_nth)
qed (auto simp: accessible_regs_def)

lemma available_reg_caps_accessed_reg_caps[simp]:
  "available_reg_caps CC ISA i t = accessed_reg_caps (run initial (take i t))"
  by (induction i) (auto simp: available_reg_caps_Suc take_Suc_conv_app_nth)

lemma available_mem_caps_accessed_reg_caps[simp]:
  "available_mem_caps CC ISA i t = accessed_mem_caps (run initial (take i t))"
  by (induction i) (auto simp: available_mem_caps_Suc take_Suc_conv_app_nth)

lemma accessed_caps_run_take_eq[simp]:
  "available_caps CC ISA use_mem_caps i t = accessed_caps use_mem_caps (run initial (take i t))"
  by (cases i) (auto simp: available_caps.simps accessed_caps_def)

lemma read_from_KCC_run_take_eq:
  "read_from_KCC (run initial (take i t)) = {v. \<exists>r j. j < i \<and> j < length t \<and> t ! j = E_read_reg r v \<and> r \<in> KCC ISA}"
proof (induction i)
  case (Suc i)
  then show ?case
    using system_reg_access_run_take_eq(1)[of i t]
    by (cases "i < length t") (auto simp: take_Suc_conv_app_nth less_Suc_eq)
qed auto

lemma write_only_regs_run_take_eq:
  "written_regs (run initial (take i t)) = {r. \<exists>v c j. t ! j = E_write_reg r v \<and> j < i \<and> j < length t \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
proof (induction i)
  case (Suc i)
  then show ?case
    by (cases "i < length t") (auto simp: take_Suc_conv_app_nth less_Suc_eq)
qed auto

lemma privileged_accessible_system_reg_access:
  assumes "r \<in> accessible_regs s" and "r \<in> privileged_regs ISA"
  shows "system_reg_access s"
  using assms
  by (auto simp: accessible_regs_def)

fun trace_allows_system_reg_access where
  "trace_allows_system_reg_access [] s = False"
| "trace_allows_system_reg_access (e # t) s =
     (allows_system_reg_access (accessible_regs s) e \<or>
      trace_allows_system_reg_access t (axiom_step s e))"

lemma trace_allows_system_reg_access_append[simp]:
  "trace_allows_system_reg_access (t1 @ t2) s
  \<longleftrightarrow> trace_allows_system_reg_access t1 s \<or> trace_allows_system_reg_access t2 (run s t1)"
  by (induction t1 arbitrary: t2 s) auto

lemma system_reg_access_run_iff:
  "system_reg_access (run s t) \<longleftrightarrow> system_reg_access s \<or> trace_allows_system_reg_access t s"
  by (induction t s rule: trace_allows_system_reg_access.induct) auto

lemma system_reg_access_accessible_regs:
  assumes "system_reg_access s"
    and "Rs - (privileged_regs ISA - (PCC ISA \<union> IDC ISA)) \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs s"
  using assms
  by (auto simp: accessible_regs_def)

lemmas step_defs = axiom_step_def reads_mem_cap_def

abbreviation "special_reg_names \<equiv> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA"

definition non_cap_reg :: "('regstate, 'regval, 'a) register_ref \<Rightarrow> bool" where
  "non_cap_reg r \<equiv>
     name r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<and>
     (\<forall>rv v. of_regval r rv = Some v \<longrightarrow> caps_of_regval ISA rv = {}) \<and>
     (\<forall>v. caps_of_regval ISA (regval_of r v) = {})"

fun non_cap_event :: "'regval event \<Rightarrow> bool" where
  "non_cap_event (E_read_reg r v) = (r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<and> caps_of_regval ISA v = {})"
| "non_cap_event (E_write_reg r v) = (r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<and> caps_of_regval ISA v = {})"
| "non_cap_event (E_read_memt _ _ _ _) = False"
| "non_cap_event (E_read_mem _ _ _ _) = False"
| "non_cap_event (E_write_memt _ _ _ _ _ _) = False"
| "non_cap_event (E_write_mem _ _ _ _ _) = False"
| "non_cap_event _ = True"

fun non_mem_event :: "'regval event \<Rightarrow> bool" where
  "non_mem_event (E_read_memt _ _ _ _) = False"
| "non_mem_event (E_read_mem _ _ _ _) = False"
| "non_mem_event (E_write_memt _ _ _ _ _ _) = False"
| "non_mem_event (E_write_mem _ _ _ _ _) = False"
| "non_mem_event _ = True"

definition non_cap_trace :: "'regval trace \<Rightarrow> bool" where
  "non_cap_trace t \<equiv> (\<forall>e \<in> set t. non_cap_event e)"

definition non_mem_trace :: "'regval trace \<Rightarrow> bool" where
  "non_mem_trace t \<equiv> (\<forall>e \<in> set t. non_mem_event e)"

lemma non_cap_trace_Nil[intro, simp]:
  "non_cap_trace []"
  by (auto simp: non_cap_trace_def)

lemma non_cap_trace_Cons[iff]:
  "non_cap_trace (e # t) \<longleftrightarrow> non_cap_event e \<and> non_cap_trace t"
  by (auto simp: non_cap_trace_def)

lemma non_cap_trace_append[iff]:
  "non_cap_trace (t1 @ t2) \<longleftrightarrow> non_cap_trace t1 \<and> non_cap_trace t2"
  by (induction t1) auto

lemma non_mem_trace_Nil[intro, simp]:
  "non_mem_trace []"
  by (auto simp: non_mem_trace_def)

lemma non_mem_trace_Cons[iff]:
  "non_mem_trace (e # t) \<longleftrightarrow> non_mem_event e \<and> non_mem_trace t"
  by (auto simp: non_mem_trace_def)

lemma non_mem_trace_append[iff]:
  "non_mem_trace (t1 @ t2) \<longleftrightarrow> non_mem_trace t1 \<and> non_mem_trace t2"
  by (induction t1) auto

lemma non_cap_event_non_mem_event:
  "non_mem_event e" if "non_cap_event e"
  using that
  by (cases e) auto

lemma non_cap_trace_non_mem_trace:
  "non_mem_trace t" if "non_cap_trace t"
  using that
  by (auto simp: non_mem_trace_def non_cap_trace_def intro: non_cap_event_non_mem_event)

lemma non_cap_event_axiom_step_inv:
  assumes "non_cap_event e"
  shows "axiom_step s e = s"
  using assms
  by (elim non_cap_event.elims) (auto simp: step_defs bind_eq_Some_conv split: option.splits)

lemma non_cap_trace_run_inv:
  assumes "non_cap_trace t"
  shows "run s t = s"
  using assms
  by (induction t) (auto simp: non_cap_event_axiom_step_inv)

definition non_cap_exp :: "('regval, 'a, 'exception) monad \<Rightarrow> bool" where
  "non_cap_exp m = (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> (non_cap_trace t \<or> (\<exists>t' r v msg. t = t' @ [E_read_reg r v] \<and> r \<notin> special_reg_names \<and> non_cap_trace t' \<and> m' = Fail msg)))"

definition non_mem_exp :: "('regval, 'a, 'exception) monad \<Rightarrow> bool" where
  "non_mem_exp m = (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> non_mem_trace t)"

lemma non_cap_exp_Traces_cases:
  assumes "non_cap_exp m"
    and "(m, t, m') \<in> Traces"
  obtains (Non_cap) "non_cap_trace t"
  | (Fail) t' r v msg where "t = t' @ [E_read_reg r v]" and "r \<notin> special_reg_names" and "m' = Fail msg" and "non_cap_trace t'"
  using assms
  unfolding non_cap_exp_def
  by blast

lemma non_cap_exp_non_mem_exp:
  "non_mem_exp m" if "non_cap_exp m"
  by (auto simp: non_mem_exp_def elim!: non_cap_exp_Traces_cases[OF that] intro: non_cap_trace_non_mem_trace)

lemma non_cap_exp_Run_non_cap_trace:
  assumes m: "non_cap_exp m"
    and t: "Run m t a"
  shows "non_cap_trace t"
  using t
  by (elim non_cap_exp_Traces_cases[OF m]) auto

lemmas non_cap_exp_Run_run_invI = non_cap_exp_Run_non_cap_trace[THEN non_cap_trace_run_inv]

named_theorems non_cap_expI
named_theorems non_mem_expI

lemma non_cap_exp_return[non_cap_expI]:
  "non_cap_exp (return a)"
  by (auto simp: non_cap_exp_def return_def)

lemma non_cap_exp_bindI[intro!]:
  assumes m: "non_cap_exp m"
    and f: "\<And>t a. Run m t a \<Longrightarrow> non_cap_exp (f a)"
  shows "non_cap_exp (m \<bind> f)"
proof (unfold non_cap_exp_def, intro allI impI)
  fix t m'
  assume "(m \<bind> f, t, m') \<in> Traces"
  then show "non_cap_trace t \<or> (\<exists>t' r v msg. t = t' @ [E_read_reg r v] \<and> r \<notin> special_reg_names \<and> non_cap_trace t' \<and> m' = Fail msg)"
  proof (cases rule: bind_Traces_cases)
    case (Left m'')
    then show ?thesis
      by (elim non_cap_exp_Traces_cases[OF m]) auto
  next
    case (Bind tm am tf)
    then show ?thesis
      using non_cap_exp_Run_non_cap_trace[OF m \<open>Run m tm am\<close>]
      by (elim f[OF \<open>Run m tm am\<close>, THEN non_cap_exp_Traces_cases]) auto
  qed
qed

lemma non_mem_exp_bindI[intro!]:
  assumes "non_mem_exp m"
    and "\<And>t a. Run m t a \<Longrightarrow> non_mem_exp (f a)"
  shows "non_mem_exp (m \<bind> f)"
  using assms
  by (fastforce simp: non_mem_exp_def elim!: bind_Traces_cases)

lemma non_cap_exp_try_catch[intro!]:
  assumes m: "non_cap_exp m"
    and h: "\<And>t ex. (m, t, Exception ex) \<in> Traces \<Longrightarrow> non_cap_exp (h ex)"
  shows "non_cap_exp (try_catch m h)"
proof (unfold non_cap_exp_def, intro allI impI)
  fix t m'
  assume "(try_catch m h, t, m') \<in> Traces"
  then show "non_cap_trace t \<or> (\<exists>t' r v msg. t = t' @ [E_read_reg r v] \<and> r \<notin> special_reg_names \<and> non_cap_trace t' \<and> m' = Fail msg)"
  proof (cases rule: try_catch_Traces_cases)
    case (NoEx m'')
    then show ?thesis
      by (elim non_cap_exp_Traces_cases[OF m]) auto
  next
    case (Ex tm ex th)
    then show ?thesis
      by (elim non_cap_exp_Traces_cases[OF m]
               h[OF \<open>(m, tm, Exception ex) \<in> Traces\<close>, THEN non_cap_exp_Traces_cases])
         auto
  qed
qed

lemma non_mem_exp_try_catch:
  assumes "non_mem_exp m"
    and "\<And>t ex. (m, t, Exception ex) \<in> Traces \<Longrightarrow> non_mem_exp (h ex)"
  shows "non_mem_exp (try_catch m h)"
  using assms
  by (fastforce simp: non_mem_exp_def elim!: try_catch_Traces_cases)

lemma non_cap_exp_throw[non_cap_expI]:
  "non_cap_exp (throw e)"
  by (auto simp: non_cap_exp_def)

lemma non_cap_exp_early_return[non_cap_expI]:
  "non_cap_exp (early_return a)"
  by (auto simp: early_return_def intro!: non_cap_expI)

lemma non_cap_exp_catch_early_return[intro!]:
  "non_cap_exp (catch_early_return m)" if "non_cap_exp m"
  by (auto simp: catch_early_return_def intro!: that non_cap_expI split: sum.splits)

lemma non_mem_exp_catch_early_return:
  "non_mem_exp (catch_early_return m)" if "non_mem_exp m"
  by (auto simp: catch_early_return_def intro!: that non_mem_exp_try_catch non_cap_expI[THEN non_cap_exp_non_mem_exp] split: sum.splits)

lemma non_cap_exp_liftR[intro!]:
  "non_cap_exp (liftR m)" if "non_cap_exp m"
  by (auto simp: liftR_def intro!: that non_cap_expI)

lemma non_mem_exp_liftR:
  "non_mem_exp (liftR m)" if "non_mem_exp m"
  by (auto simp: liftR_def intro!: that non_mem_exp_try_catch non_cap_expI[THEN non_cap_exp_non_mem_exp])

lemma non_cap_exp_assert_exp[non_cap_expI]:
  "non_cap_exp (assert_exp c msg)"
  by (auto simp: assert_exp_def non_cap_exp_def)

lemma non_cap_exp_foreachM[intro]:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> non_cap_exp (body x vars)"
  shows "non_cap_exp (foreachM xs vars body)"
  using assms
  by (induction xs vars body rule: foreachM.induct) (auto intro: non_cap_expI)

lemma non_mem_exp_foreachM:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> non_mem_exp (body x vars)"
  shows "non_mem_exp (foreachM xs vars body)"
  using assms
  by (induction xs vars body rule: foreachM.induct) (auto intro: non_cap_expI[THEN non_cap_exp_non_mem_exp])

lemma non_cap_exp_choose_bool[non_cap_expI]:
  "non_cap_exp (choose_bool desc)"
  by (auto simp: choose_bool_def non_cap_exp_def elim: Traces_cases)

lemma non_cap_exp_undefined_bool[non_cap_expI]:
  "non_cap_exp (undefined_bool ())"
  by (auto simp: undefined_bool_def intro: non_cap_expI)

lemma non_cap_exp_bool_of_bitU_nondet[non_cap_expI]:
  "non_cap_exp (bool_of_bitU_nondet b)"
  unfolding bool_of_bitU_nondet_def
  by (cases b) (auto intro: non_cap_expI)

lemma non_cap_exp_Fail[non_cap_expI]:
  "non_cap_exp (Fail msg)"
  by (auto simp: non_cap_exp_def)

lemma non_cap_exp_maybe_fail[non_cap_expI]:
  "non_cap_exp (maybe_fail msg v)"
  by (cases v) (auto simp: maybe_fail_def intro: non_cap_expI)

lemma non_cap_exp_bool_of_bitU_fail[non_cap_expI]:
  "non_cap_exp (bool_of_bitU_fail b)"
  unfolding bool_of_bitU_fail_def
  by (cases b) (auto intro: non_cap_expI)

lemma non_cap_exp_bools_of_bits_nondet[non_cap_expI]:
  "non_cap_exp (bools_of_bits_nondet bits)"
  by (auto simp: bools_of_bits_nondet_def intro: non_cap_expI)

lemma non_cap_exp_of_bits_nondet[non_cap_expI]:
  "non_cap_exp (of_bits_nondet BC bits)"
  by (auto simp: of_bits_nondet_def intro: non_cap_expI)

lemma non_cap_exp_of_bits_fail[non_cap_expI]:
  "non_cap_exp (of_bits_fail BC bits)"
  by (auto simp: of_bits_fail_def intro: non_cap_expI)

lemma non_cap_exp_mword_nondet[non_cap_expI]:
  "non_cap_exp (mword_nondet ())"
  by (auto simp add: mword_nondet_def intro: non_cap_expI simp del: repeat.simps)

lemma non_cap_exp_genlistM:
  assumes "\<And>n. non_cap_exp (f n)"
  shows "non_cap_exp (genlistM f n)"
  using assms
  by (auto simp: genlistM_def intro!: non_cap_expI)

lemma non_cap_exp_choose_bools[non_cap_expI]:
  "non_cap_exp (choose_bools desc n)"
  by (auto simp: choose_bools_def intro: non_cap_expI non_cap_exp_genlistM)

lemma non_cap_exp_exit[non_cap_expI]:
  "non_cap_exp (exit0 ())"
  unfolding exit0_def
  by (rule non_cap_exp_Fail)

lemma non_cap_exp_chooseM[non_cap_expI]:
  "non_cap_exp (chooseM desc xs)"
  by (auto simp: chooseM_def intro!: non_cap_expI split: option.splits)

lemma non_cap_exp_internal_pick[non_cap_expI]:
  "non_cap_exp (internal_pick xs)"
  by (auto simp: internal_pick_def intro!: non_cap_expI)

lemma non_cap_exp_and_boolM[intro!]:
  "non_cap_exp (and_boolM m1 m2)" if "non_cap_exp m1" and "non_cap_exp m2"
  by (auto simp: and_boolM_def intro!: that non_cap_expI)

lemma non_mem_exp_and_boolM:
  "non_mem_exp (and_boolM m1 m2)" if "non_mem_exp m1" and "non_mem_exp m2"
  by (auto simp: and_boolM_def intro!: that non_cap_expI[THEN non_cap_exp_non_mem_exp])

lemma non_cap_exp_or_boolM[intro!]:
  "non_cap_exp (or_boolM m1 m2)" if "non_cap_exp m1" and "non_cap_exp m2"
  by (auto simp: or_boolM_def intro!: that non_cap_expI)

lemma non_mem_exp_or_boolM:
  "non_mem_exp (or_boolM m1 m2)" if "non_mem_exp m1" and "non_mem_exp m2"
  by (auto simp: or_boolM_def intro!: that non_cap_expI[THEN non_cap_exp_non_mem_exp])

lemma non_cap_exp_let[intro!]:
  "non_cap_exp (let x = a in m x)" if "non_cap_exp (m a)"
  by (auto intro: that)

lemma non_mem_exp_let:
  "non_mem_exp (let x = a in m x)" if "non_mem_exp (m a)"
  by (auto intro: that)

lemma non_cap_exp_if:
  assumes "c \<Longrightarrow> non_cap_exp m1" and "\<not>c \<Longrightarrow> non_cap_exp m2"
  shows "non_cap_exp (if c then m1 else m2)"
  using assms
  by auto

lemma non_mem_exp_if:
  assumes "c \<Longrightarrow> non_mem_exp m1" and "\<not>c \<Longrightarrow> non_mem_exp m2"
  shows "non_mem_exp (if c then m1 else m2)"
  using assms
  by auto

lemma non_cap_exp_read_non_cap_reg:
  assumes "non_cap_reg r"
  shows "non_cap_exp (read_reg r :: ('regval, 'r, 'exception) monad)"
proof -
  have "non_cap_trace t \<or> (\<exists>v msg. t = [E_read_reg (name r) v] \<and> name r \<notin> special_reg_names \<and> m' = Fail msg)"
    if "(read_reg r, t, m' :: ('regval, 'r, 'exception) monad) \<in> Traces" for t m'
    using that assms
    by (auto simp: read_reg_def non_cap_exp_def non_cap_reg_def elim!: Read_reg_TracesE split: option.splits)
  then show ?thesis
    unfolding non_cap_exp_def
    by blast
qed

lemma
  non_mem_exp_read_reg[non_mem_expI]: "non_mem_exp (read_reg r)" and
  non_mem_exp_write_reg[non_mem_expI]: "non_mem_exp (write_reg r v)"
  unfolding non_mem_exp_def read_reg_def write_reg_def
  by (auto elim!: Read_reg_TracesE Write_reg_TracesE split: option.splits)

lemma non_cap_exp_write_non_cap_reg:
  assumes "non_cap_reg r"
  shows "non_cap_exp (write_reg r v)"
  using assms
  unfolding write_reg_def
  by (auto simp: non_cap_exp_def non_cap_reg_def elim!: Write_reg_TracesE)

named_theorems non_cap_exp_split

declare option.split[where P = "non_cap_exp", non_cap_exp_split]
declare sum.split[where P = "non_cap_exp", non_cap_exp_split]
declare prod.split[where P = "non_cap_exp", non_cap_exp_split]
declare bool.split[where P = "non_cap_exp", non_cap_exp_split]

lemmas non_cap_exp_combinators =
  non_cap_exp_bindI non_cap_exp_if non_cap_exp_let non_cap_exp_and_boolM non_cap_exp_or_boolM
  non_cap_exp_foreachM non_cap_exp_try_catch non_cap_exp_catch_early_return non_cap_exp_liftR

method non_cap_expI_base uses intro =
  (intro intro non_cap_expI non_cap_exp_split[THEN iffD2] non_cap_exp_combinators
         non_cap_exp_read_non_cap_reg non_cap_exp_write_non_cap_reg allI impI conjI)

method non_cap_expI uses simp intro = (non_cap_expI_base intro: intro; simp add: simp)

declare non_mem_exp_bindI[rule del]

lemma non_cap_exp_runE:
  assumes t: "Run m t a" and m: "non_cap_exp m" and P: "P (run s t)"
  shows "P s"
  using P unfolding non_cap_exp_Run_run_invI[OF m t] .

method non_cap_exp_insert_run for s :: "('cap, 'regval) axiom_state" =
  (match premises in t: \<open>Run m t a\<close> for m t a \<Rightarrow>
     \<open>rule non_cap_exp_runE[where s = s, OF t], solves \<open>non_cap_expI\<close>\<close>)

named_theorems non_mem_exp_split

declare option.split[where P = "non_mem_exp", non_mem_exp_split]
declare sum.split[where P = "non_mem_exp", non_mem_exp_split]
declare prod.split[where P = "non_mem_exp", non_mem_exp_split]
declare bool.split[where P = "non_mem_exp", non_mem_exp_split]

lemmas non_mem_exp_combinators =
  non_mem_exp_bindI non_mem_exp_if non_mem_exp_let non_mem_exp_and_boolM non_mem_exp_or_boolM
  non_mem_exp_foreachM non_mem_exp_try_catch non_mem_exp_catch_early_return non_mem_exp_liftR

method non_mem_expI uses simp intro =
  (intro intro non_mem_expI non_mem_exp_split[THEN iffD2] non_mem_exp_combinators
         non_cap_expI[THEN non_cap_exp_non_mem_exp] allI impI conjI;
   simp add: simp)

lemma Run_write_reg_no_cap[trace_simp]:
  assumes "Run (write_reg r v) t a"
    and "non_cap_reg r"
  shows "run s t = s"
  using assms
  by (cases s) (auto simp: write_reg_def step_defs non_cap_reg_def elim!: Write_reg_TracesE)

lemma Run_write_reg_run_gen:
  assumes "Run (write_reg r v) t a"
  shows "run s t =
           s\<lparr>written_regs := written_regs s \<union>
                                (if (\<exists>c \<in> caps_of_regval ISA (regval_of r v). is_tagged_method CC c)
                                 then {name r} else {})\<rparr>"
  using assms
  by (cases s) (auto simp: write_reg_def step_defs elim!: Write_reg_TracesE)

lemma Run_read_non_cap_reg_run[trace_simp]:
  assumes "Run (read_reg r) t v"
    and "non_cap_reg r"
  shows "run s t = s"
  using assms
  by (auto simp: step_defs non_cap_reg_def elim!: Run_read_regE)

lemma no_reg_writes_to_written_regs_run_inv[trace_simp]:
  assumes "Run m t a"
    and "no_reg_writes_to UNIV m"
  shows "written_regs (run s t) = written_regs s"
proof -
  have "E_write_reg r v \<notin> set t" for r v
    using assms
    by (auto simp: no_reg_writes_to_def)
  then show ?thesis
    by (induction t rule: rev_induct) auto
qed

method trace_enabledI uses simp elim =
  (auto simp: simp trace_simp elim!: elim trace_elim)

lemma non_special_reg_accessible:
  "r \<in> accessible_regs s" if "r \<notin> special_reg_names"
  using that
  by (auto simp: accessible_regs_def)

lemma non_special_regs_accessible:
  "Rs \<subseteq> accessible_regs s" if "Rs \<inter> special_reg_names = {}"
  using that
  by (auto simp: accessible_regs_def)

lemma accessible_regs_no_writes_trace:
  assumes "r \<in> PCC ISA \<union> IDC ISA \<longrightarrow> (\<forall>v. E_write_reg r v \<notin> set t)"
    and "r \<in> accessible_regs s"
  shows "r \<in> accessible_regs (run s t)"
proof (use assms in \<open>induction t arbitrary: s\<close>)
  case (Cons e t)
  show ?case
    using Cons.prems Cons.IH[of "axiom_step s e"]
    by (auto simp: accessible_regs_def)
qed simp

lemma accessible_regs_no_writes_run:
  assumes t: "Run m t a"
    and m: "r \<in> PCC ISA \<union> IDC ISA \<longrightarrow> runs_no_reg_writes_to {r} m"
    and s: "r \<in> accessible_regs s"
  shows "r \<in> accessible_regs (run s t)"
  using assms
  by (intro accessible_regs_no_writes_trace) (auto simp: runs_no_reg_writes_to_def)

lemma no_reg_writes_to_mono:
  assumes "runs_no_reg_writes_to Rs m"
    and "Rs' \<subseteq> Rs"
  shows "runs_no_reg_writes_to Rs' m"
  using assms
  by (auto simp: runs_no_reg_writes_to_def)

lemma accessible_regs_no_writes_run_subset:
  assumes t: "Run m t a" and m: "runs_no_reg_writes_to (Rs \<inter> (PCC ISA \<union> IDC ISA)) m"
    and Rs: "Rs \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using t Rs no_reg_writes_to_mono[OF m]
  by (auto intro: accessible_regs_no_writes_run)

(*method accessible_regsI uses simp assms =
  (match conclusion in \<open>Rs \<subseteq> accessible_regs (run s t)\<close> for Rs s t \<Rightarrow>
     \<open>match premises in t: \<open>Run_inv m t a regs\<close> for m a regs \<Rightarrow>
        \<open>rule accessible_regs_no_writes_run_subset[OF t],
         solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>,
         accessible_regsI simp: simp assms: assms\<close>\<close>\<close>
   \<bar> \<open>Rs \<subseteq> accessible_regs s\<close> for Rs s \<Rightarrow> \<open>use assms in \<open>auto simp: simp\<close>\<close>)*)

named_theorems accessible_regsE
named_theorems accessible_regsI

method accessible_regs_subsetI uses assms =
  (match conclusion in \<open>Rs \<subseteq> accessible_regs s\<close> for Rs s \<Rightarrow>
     \<open>match assms in Rs': "Rs' \<subseteq> accessible_regs s" for Rs' \<Rightarrow>
        \<open>rule subset_trans[OF _ Rs'];
         solves \<open>intro insert_subsetI empty_subsetI insertI1 insertI2\<close>\<close>\<close>)

method accessible_regs_step uses simp assms =
  ((erule accessible_regsE eqTrueE)
    | (rule accessible_regsI TrueI)
    | (erule accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>)
    | (solves \<open>accessible_regs_subsetI assms: assms\<close>))

method accessible_regsI_with methods solve uses simp assms =
  ((erule accessible_regsE eqTrueE; accessible_regsI_with solve simp: simp assms: assms)
    | (rule accessible_regsI TrueI; accessible_regsI_with solve simp: simp assms: assms)
    | (erule accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>,
       accessible_regsI_with solve simp: simp assms: assms)
    | (solves \<open>accessible_regs_subsetI assms: assms\<close>)
    | (rule non_special_regs_accessible non_special_reg_accessible,
       solves \<open>solve\<close>)
    | solve)

method accessible_regsI uses simp assms =
  (accessible_regsI_with
     \<open>(use assms in \<open>no_reg_writes_toI simp: simp\<close>)
       | (use assms in \<open>auto simp: simp\<close>)\<close>
     simp: simp assms: assms)

definition derivable_caps :: "('cap, 'regval) axiom_state \<Rightarrow> 'cap set" where
  "derivable_caps s \<equiv> {c. is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_caps use_mem_caps s)}"

definition derivable_mem_caps where
  "derivable_mem_caps s = {c. is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_mem_caps s)}"

definition accessed_mem_caps_of_trace where
  "accessed_mem_caps_of_trace t = (\<Union>e \<in> set t. accessed_mem_caps_of_ev e)"

lemma accessed_mem_caps_of_trace_append[simp]:
  "accessed_mem_caps_of_trace (t @ t') = accessed_mem_caps_of_trace t \<union> accessed_mem_caps_of_trace t'"
  by (auto simp: accessed_mem_caps_of_trace_def)

lemma accessed_mem_caps_of_trace_Nil[simp]:
  "accessed_mem_caps_of_trace [] = {}"
  by (auto simp: accessed_mem_caps_of_trace_def)

lemma accessed_mem_caps_of_trace_Cons[simp]:
  "accessed_mem_caps_of_trace (e # t) = accessed_mem_caps_of_ev e \<union> accessed_mem_caps_of_trace t"
  by (auto simp: accessed_mem_caps_of_trace_def)

lemma accessed_mem_caps_of_trace_accessed_mem_caps_run:
  assumes "c \<in> accessed_mem_caps_of_trace t"
  shows "c \<in> accessed_mem_caps (run s t)"
  using assms
  by (induction t rule: rev_induct) auto

lemma accessed_mem_caps_derivable_mem_caps:
  assumes "is_tagged_method CC c \<longrightarrow> c \<in> accessed_mem_caps s"
  shows "c \<in> derivable_mem_caps s"
  using assms
  by (auto simp: derivable_mem_caps_def intro: derivable.Copy)

definition accessed_mem_cap_of_trace_if_tagged where
  "accessed_mem_cap_of_trace_if_tagged c t \<equiv>
     is_tagged_method CC c \<longrightarrow> c \<in> accessed_mem_caps_of_trace t"

lemma accessed_mem_cap_of_trace_if_tagged_append[simp]:
  "accessed_mem_cap_of_trace_if_tagged c (t @ t') \<longleftrightarrow>
   accessed_mem_cap_of_trace_if_tagged c t \<or> accessed_mem_cap_of_trace_if_tagged c t'"
  by (auto simp: accessed_mem_cap_of_trace_if_tagged_def)

lemma untagged_accessed_mem_cap_of_trace[simp]:
  assumes "\<not>is_tagged_method CC c"
  shows "accessed_mem_cap_of_trace_if_tagged c t"
  using assms
  by (auto simp: accessed_mem_cap_of_trace_if_tagged_def)

lemma accessed_mem_cap_of_trace_derivable_mem_cap:
  assumes "accessed_mem_cap_of_trace_if_tagged c t"
  shows "c \<in> derivable_mem_caps (run s t)"
  using assms
  unfolding accessed_mem_cap_of_trace_if_tagged_def
  by (auto intro: accessed_mem_caps_derivable_mem_caps accessed_mem_caps_of_trace_accessed_mem_caps_run)

lemma derivable_mem_caps_derivable_caps:
  assumes "c \<in> derivable_mem_caps s"
    and "use_mem_caps"
  shows "c \<in> derivable_caps s"
  using assms(1)
  using derivable_mono[of "accessed_mem_caps s" "accessed_reg_caps s \<union> accessed_mem_caps s"]
  by (auto simp: derivable_mem_caps_def derivable_caps_def accessed_caps_def intro: assms(2))

named_theorems derivable_capsE
named_theorems derivable_capsI

lemma accessed_reg_caps_run_mono:
  "accessed_reg_caps s \<subseteq> accessed_reg_caps (run s t)"
  by (rule subsetI) (induction t arbitrary: s; auto)

lemma accessed_mem_caps_run_mono:
  "accessed_mem_caps s \<subseteq> accessed_mem_caps (run s t)"
  by (rule subsetI) (induction t arbitrary: s; auto)

lemma accessed_caps_run_mono:
  "accessed_caps use_mem_caps s \<subseteq> accessed_caps use_mem_caps (run s t)"
  using accessed_reg_caps_run_mono accessed_mem_caps_run_mono
  unfolding accessed_caps_def
  by (intro Un_mono) auto

lemma derivable_caps_run_mono:
  "derivable_caps s \<subseteq> derivable_caps (run s t)"
  using derivable_mono[OF accessed_caps_run_mono]
  by (auto simp: derivable_caps_def)

lemma derivable_caps_run_imp:
  "c \<in> derivable_caps s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  using derivable_caps_run_mono
  by auto

named_theorems derivable_caps_runI

declare derivable_caps_run_imp[derivable_caps_runI]

lemma system_reg_access_run_or_exI[derivable_caps_runI]:
  assumes "system_reg_access s \<or> ex_traces"
  shows "system_reg_access (run s t) \<or> ex_traces"
  using assms
  unfolding system_reg_access_run_iff
  by auto

named_theorems derivable_caps_combinators

lemma bind_derivable_caps[derivable_caps_combinators]:
  assumes "Run (m \<bind> f) t a"
    and "\<And>tm am tf. Run m tm am \<Longrightarrow> Run (f am) tf a \<Longrightarrow> t = tm @ tf \<Longrightarrow> c \<in> derivable_caps (run (run s tm) tf)"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (auto elim: Run_bindE)

lemma read_reg_derivable:
  assumes "Run (read_reg r) t a" and "{name r} \<subseteq> accessible_regs s"
    and "\<forall>rv. of_regval r rv = Some a \<longrightarrow> c \<in> caps_of_regval ISA rv"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (auto elim!: Run_read_regE intro!: derivable.Copy simp: derivable_caps_def accessed_caps_def)

declare Run_ifE[where thesis = "c \<in> derivable_caps (run s t)" and t = t for c s t, derivable_caps_combinators]
declare Run_letE[where thesis = "c \<in> derivable_caps (run s t)" and t = t for c s t, derivable_caps_combinators]
declare Run_ifE[where thesis = "c \<in> derivable_caps s" and a = c for c s, derivable_caps_combinators]
declare Run_letE[where thesis = "c \<in> derivable_caps s" and a = c for c s, derivable_caps_combinators]
declare Run_bindE[where thesis = "c \<in> derivable_caps s" and a = c for c s, derivable_caps_combinators]

text \<open>The above elimination rules sometimes eliminate binds at earlier points in the trace
  without reflecting the deconstruction of the trace in the goal (only in the assumptions).
  The following rule allows us to get back on track once we reach the right point in the trace.\<close>

lemma run_append_derivable_capsE[derivable_caps_combinators]:
  assumes "t = t1 @ t2"
    and "t = t1 @ t2 \<longrightarrow> c \<in> derivable_caps (run (run s t1) t2)"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by auto

lemma return_derivable_caps[derivable_capsE]:
  assumes "Run (return a) t c"
    and "a \<in> derivable_caps s"
  shows "c \<in> derivable_caps s"
  using assms
  by auto

lemma if_derivable_capsI[derivable_capsI]:
  assumes "b \<Longrightarrow> c1 \<in> derivable_caps s" and "\<not>b \<Longrightarrow> c2 \<in> derivable_caps s"
  shows "(if b then c1 else c2) \<in> derivable_caps s"
  using assms
  by auto

method derivable_caps_step =
  (rule derivable_capsI allI impI conjI
      | erule derivable_capsE conjE
      | erule derivable_caps_combinators eqTrueE
      | rule derivable_caps_runI)

method derivable_capsI_with methods solve uses intro elim simp assms =
  ((rule intro derivable_capsI allI impI conjI
      | erule elim derivable_capsE conjE
      | erule derivable_caps_combinators eqTrueE
      | rule derivable_caps_runI
      | solve (*
      | solves \<open>use assms in \<open>auto simp: simp\<close>\<close>*))+;
   derivable_capsI_with solve intro: intro elim: elim simp: simp assms: assms)

method derivable_capsI uses intro elim simp assms =
  (derivable_capsI_with
     \<open>(solves \<open>accessible_regsI simp: simp assms: assms\<close>)\<close>
     intro: intro elim: elim simp: simp assms: assms)

end

(*locale Store_Cap_Mem_Automaton = Capability_ISA CC ISA
  for CC :: "'cap Capability_class"
  and ISA :: "('cap, 'regval, 'instr, 'e) isa"
begin

definition enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s e \<equiv> (\<forall> c. \<forall> addr. \<forall> sz. 
     ((writes_mem_cap CC e = Some (addr, sz, c)) \<and> (is_tagged_method   CC) c)
     \<longrightarrow>
     (c \<in> derivable (accessed_caps s)))"

sublocale Cap_Axiom_Automaton CC ISA enabled ..

lemma non_cap_event_enabledI:
  assumes "non_cap_event e"
  shows "enabled s e"
  using assms
  by (elim non_cap_event.elims) (auto simp: enabled_def writes_mem_cap_def bind_eq_Some_conv)

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabledI non_cap_event_axiom_step_inv)

lemma enabled_E_read_reg:
  "enabled s (E_read_reg r v)"
  by (auto simp: enabled_def writes_mem_cap_def)

lemma non_cap_exp_trace_enabledI:
  assumes "non_cap_exp m"
    and "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF assms])
     (auto intro: non_cap_trace_enabledI enabled_E_read_reg simp: trace_enabled_append_iff)

lemma recognises_store_cap_mem_axiom:
  "store_cap_mem_axiom CC ISA t \<longleftrightarrow> accepts t"
  by (auto simp: accepts_from_iff_all_enabled_final store_cap_mem_axiom_def enabled_def
                 cap_derivable_iff_derivable writes_mem_cap_Some_iff)

end*)

locale Write_Cap_Automaton = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes ex_traces :: bool and invoked_caps :: "'cap set" and invoked_indirect_caps :: "'cap set"
begin

abbreviation invokes_indirect_caps where "invokes_indirect_caps \<equiv> (invoked_indirect_caps \<noteq> {})"

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_write_reg r v) =
     (\<forall>c. (c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c)
         \<longrightarrow>
         (c \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s) \<or>
          (c \<in> exception_targets ISA (read_from_KCC s) \<and> ex_traces \<and> r \<in> PCC ISA) \<or>
          (\<exists>cs. c \<in> invoked_caps \<and> cs \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s) \<and>
                is_sentry_method CC cs \<and> is_sealed_method CC cs \<and>
                leq_cap CC c (unseal_method CC cs) \<and> r \<in> PCC ISA) \<or>
          (\<exists>cs. c \<in> invoked_indirect_caps \<and> cs \<in> derivable (accessed_reg_caps s) \<and>
                is_indirect_sentry_method CC cs \<and> is_sealed_method CC cs \<and>
                leq_cap CC c (unseal_method CC cs) \<and> r \<in> IDC ISA) \<or>
          (\<exists>cc cd. c \<in> invoked_caps \<and> invokable CC cc cd \<and>
                   cc \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s) \<and>
                   cd \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s) \<and>
                   (r \<in> PCC ISA \<and> leq_cap CC c (unseal_method CC cc) \<or>
                    r \<in> IDC ISA \<and> leq_cap CC c (unseal_method CC cd))) \<or>
          (\<exists>c'. c \<in> invoked_caps \<and>
                c' \<in> derivable (accessed_mem_caps s) \<and>
                ((leq_cap CC c (unseal_method CC c') \<and> is_sealed_method CC c' \<and> is_sentry_method CC c' \<and> r \<in> PCC ISA) \<or>
                 (leq_cap CC c c' \<and> r \<in> PCC ISA \<union> IDC ISA)))))"
| "enabled s (E_read_reg r v) = (r \<in> privileged_regs ISA \<longrightarrow> (system_reg_access s \<or> ex_traces))"
| "enabled s (E_write_memt _ addr sz bytes tag _) =
     (\<forall>c.  cap_of_mem_bytes_method CC bytes tag = Some c \<and> is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s))"
| "enabled s _ = True"

lemma enabled_E_write_reg_cases:
  assumes "enabled s (E_write_reg r v)"
    and "c \<in> caps_of_regval ISA v"
    and "is_tagged_method CC c"
  obtains (Derivable) "c \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s)"
  | (KCC) "c \<in> exception_targets ISA (read_from_KCC s)" and "ex_traces" and
      "r \<in> PCC ISA" and "c \<notin> derivable (accessed_caps (\<not>invokes_indirect_caps) s)"
  | (Sentry) cs where "c \<in> invoked_caps" and "cs \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s)" and
      "is_sentry_method CC cs" and "is_sealed_method CC cs" and
      "leq_cap CC c (unseal_method CC cs)" and "r \<in> PCC ISA"
  | (SentryIndirect) cs where "c \<in> invoked_indirect_caps" and "cs \<in> derivable (accessed_reg_caps s)" and
      "is_indirect_sentry_method CC cs" and "is_sealed_method CC cs" and
      "leq_cap CC c (unseal_method CC cs)" and "r \<in> IDC ISA"
  | (CCall) cc cd where "c \<in> invoked_caps" and "invokable CC cc cd" and
      "cc \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s)" and
      "cd \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s)" and
      "r \<in> PCC ISA \<and> leq_cap CC c (unseal_method CC cc) \<or> r \<in> IDC ISA \<and> leq_cap CC c (unseal_method CC cd)" and
      "c \<notin> derivable (accessed_caps (\<not>invokes_indirect_caps) s)"
  | (Indirect) c' where "c \<in> invoked_caps" and
      "c' \<in> derivable (accessed_mem_caps s)"
      "(leq_cap CC c (unseal_method CC c') \<and> is_sealed_method CC c' \<and> is_sentry_method CC c' \<and> r \<in> PCC ISA) \<or>
       (leq_cap CC c c' \<and> r \<in> PCC ISA \<union> IDC ISA)"
  using assms
  by (cases "c \<in> derivable (accessed_caps (\<not>invokes_indirect_caps) s)"; auto; fastforce)

sublocale Cap_Axiom_Automaton CC ISA enabled "invoked_indirect_caps = {}" ..

lemma non_cap_event_enabledI:
  assumes "non_cap_event e"
  shows "enabled s e"
  using assms
  by (elim non_cap_event.elims) auto

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabledI non_cap_event_axiom_step_inv)

lemma non_cap_exp_trace_enabledI:
  assumes "non_cap_exp m"
    and "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF assms])
     (auto intro: non_cap_trace_enabledI simp: trace_enabled_append_iff)

(*lemma accepts_E_write_reg_not_read_after:
  assumes "accepts t"
    and "i < length t"
    and "index t i = Some (E_write_reg r v)"
    and "c \<in> caps_of_regval ISA v"
    and "is_tagged_method CC c"
    and "c \<notin> derivable (available_caps CC ISA i t)"
    and "r \<in> PCC ISA \<or> r \<in> IDC ISA"
  shows "reg_not_read_after i r t"
  using assms
  unfolding accepts_from_iff_all_enabled_final reg_not_read_after_def
  by (auto elim!: enabled.elims simp: write_only_regs_run_take_eq)*)

lemma index_eq_some': "(index l n = Some x) = (n < length l \<and> l ! n = x)"
  by auto

lemma recognises_store_cap_reg_read_reg_axioms:
  assumes t: "accepts t"
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps invoked_indirect_caps t"
    and "store_cap_mem_axiom CC ISA invoked_indirect_caps t"
    and "read_reg_axiom CC ISA ex_traces t"
proof -
  show "read_reg_axiom CC ISA ex_traces t"
    using assms (*read_from_KCC_run_take_eq[of "length t" t]*)
    unfolding accepts_from_iff_all_enabled_final read_reg_axiom_def
    by (auto elim!: enabled.elims)
  show "store_cap_reg_axiom CC ISA ex_traces invoked_caps invoked_indirect_caps t"
  proof (unfold store_cap_reg_axiom_def, intro allI impI, goal_cases Idx)
    case (Idx i c r)
    then show ?case
    proof cases
      assume i: "i < length t"
      then obtain v where e: "index t i = Some (E_write_reg r v)"
        and c: "c \<in> caps_of_regval ISA v"
        and tag: "is_tagged_method CC c"
        using Idx
        by (cases "t ! i") auto
      then have "enabled (run initial (take i t)) (E_write_reg r v)"
        using accepts_from_nth_enabledI[OF t i]
        by auto
      from this c tag
      show ?thesis
      proof (cases rule: enabled_E_write_reg_cases)
        case Derivable
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      next
        case KCC
        (*then obtain r' j
          where v': "t ! j = E_read_reg r' v'" and j: "j < i" and r': "r' \<in> KCC ISA"
          by (auto simp: read_from_KCC_run_take_eq)*)
        show ?thesis
          using (*j i v'[symmetric] r'*) KCC
          unfolding index_eq_some'
          by (auto simp: cap_derivable_iff_derivable read_from_KCC_run_take_eq)
      next
        case (Sentry cs)
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      next
        case (SentryIndirect cs)
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      next
        case (CCall cc cd)
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      next
        case (Indirect c')
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      qed
    qed auto
  qed
  show "store_cap_mem_axiom CC ISA invoked_indirect_caps t"
    using assms
    unfolding accepts_from_iff_all_enabled_final store_cap_mem_axiom_def
    by (auto simp: cap_derivable_iff_derivable writes_mem_cap_Some_iff)
qed

end

locale Cap_Axiom_Assm_Automaton = Cap_Axiom_Automaton CC ISA enabled use_mem_caps
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool"
    and use_mem_caps :: bool +
  fixes ex_traces :: bool
    and ev_assms :: "'regval event \<Rightarrow> bool"
  assumes non_cap_event_enabled: "\<And>e. non_cap_event e \<Longrightarrow> enabled s e"
    and read_non_special_regs_enabled: "\<And>r v. r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<Longrightarrow> enabled s (E_read_reg r v)"
begin

definition "trace_assms t \<equiv> \<forall>e \<in> set t. ev_assms e"

lemma trace_assms_append[iff]: "trace_assms (t1 @ t2) \<longleftrightarrow> trace_assms t1 \<and> trace_assms t2"
  by (auto simp: trace_assms_def)

lemma trace_assms_Nil[simp, intro]: "trace_assms []"
  by (auto simp: trace_assms_def)

lemma trace_assms_Cons[iff]: "trace_assms (e # t) \<longleftrightarrow> ev_assms e \<and> trace_assms t"
  by (auto simp: trace_assms_def)

definition "isException m \<equiv> ((\<exists>e. m = Exception e) \<or> (\<exists>msg. m = Fail msg)) \<and> ex_traces"

definition finished :: "('regval,'a,'ex) monad \<Rightarrow> bool" where
  "finished m = ((\<exists>a. m = Done a) \<or> isException m)"

lemma finishedE:
  assumes "finished m"
  obtains (Done) a where "m = Done a"
  | (Ex) "isException m"
  using assms
  by (auto simp: finished_def)

lemma finished_cases:
  assumes "finished m"
  obtains (Done) a where "m = Done a" | (Fail) msg where "m = Fail msg" | (Ex) e where "m = Exception e"
  using assms
  by (auto simp: finished_def isException_def)

lemma finished_Done[intro, simp]:
  "finished (Done a)"
  by (auto simp: finished_def)

lemma finished_Fail[intro, simp]:
  "finished (Fail msg) \<Longrightarrow> finished (Fail msg')"
  unfolding finished_def isException_def
  by auto

lemma finished_Exception[intro, simp]:
  "finished (Exception e) \<Longrightarrow> finished (Exception e')"
  unfolding finished_def isException_def
  by auto

lemma finished_isException[intro, simp]:
  "isException m \<Longrightarrow> finished m"
  by (auto simp: finished_def)

lemma finished_bind_left:
  assumes "finished (m \<bind> f)"
  shows "finished m"
  using assms
  unfolding finished_def isException_def
  by (cases m) auto

definition
  "traces_enabled m s \<equiv>
     \<forall>t m'. (m, t, m') \<in> Traces \<and> finished m' \<and> trace_assms t \<longrightarrow> trace_enabled s t"

lemma traces_enabled_accepts_fromI:
  assumes "hasTrace t m" and "traces_enabled m s" and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
    and "trace_assms t"
  shows "accepts_from s t"
  using assms
  unfolding traces_enabled_def finished_def isException_def
  unfolding hasTrace_iff_Traces_final hasException_iff_Traces_Exception hasFailure_iff_Traces_Fail
  unfolding runTrace_iff_Traces[symmetric]
  by (intro trace_enabled_acceptI) (auto elim!: final_cases)

named_theorems traces_enabledI

lemma traces_enabled_bind[traces_enabledI]:
  assumes "traces_enabled m s"
    and "\<And>t a. Run m t a \<Longrightarrow> trace_assms t \<Longrightarrow> traces_enabled (f a) (run s t)"
  shows "traces_enabled (m \<bind> f) s"
  using assms
  by (auto simp: traces_enabled_def trace_enabled_append_iff
      elim!: bind_Traces_cases dest!: finished_bind_left;
      fastforce)

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabled non_cap_event_axiom_step_inv)

lemma non_cap_exp_trace_enabledI:
  assumes m: "non_cap_exp m"
    and t: "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF m t])
     (auto intro: non_cap_trace_enabledI read_non_special_regs_enabled simp: trace_enabled_append_iff)

lemma non_cap_exp_traces_enabledI:
  assumes "non_cap_exp m"
  shows "traces_enabled m s"
  using assms
  by (auto simp: traces_enabled_def intro: non_cap_exp_trace_enabledI)

lemma exp_fails_traces_enabled:
  assumes "exp_fails m"
    and "ex_traces \<longrightarrow> traces_enabled m s"
  shows "traces_enabled m s"
  using assms
  unfolding traces_enabled_def finished_def isException_def
  by blast

lemma traces_enabled_let[traces_enabledI]:
  assumes "traces_enabled (f y) s"
  shows "traces_enabled (let x = y in f x) s"
  using assms
  by auto

lemma traces_enabled_case_prod[traces_enabledI]:
  assumes "\<And>x y. z = (x, y) \<Longrightarrow> traces_enabled (f x y) s"
  shows "traces_enabled (case z of (x, y) \<Rightarrow> f x y) s"
  using assms
  by auto

lemma traces_enabled_if[traces_enabledI]:
  assumes "c \<Longrightarrow> traces_enabled m1 s" and "\<not>c \<Longrightarrow> traces_enabled m2 s"
  shows "traces_enabled (if c then m1 else m2) s"
  using assms
  by auto

lemma traces_enabled_if_ignore_cond:
  assumes "traces_enabled m1 s" and "traces_enabled m2 s"
  shows "traces_enabled (if c then m1 else m2) s"
  using assms
  by auto

lemma traces_enabled_and_boolM[traces_enabledI]:
  assumes "traces_enabled m1 s"
    and "\<And>t. Run m1 t True \<Longrightarrow> traces_enabled m2 (run s t)"
  shows "traces_enabled (and_boolM m1 m2) s"
  using assms
  by (auto simp: and_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_or_boolM[traces_enabledI]:
  assumes "traces_enabled m1 s"
    and "\<And>t. Run m1 t False \<Longrightarrow> traces_enabled m2 (run s t)"
  shows "traces_enabled (or_boolM m1 m2) s"
  using assms
  by (auto simp: or_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_foreachM_index_list_inv:
  assumes "\<And>idx vars t.
              Inv idx vars (run s t) \<Longrightarrow>
              min from to \<le> idx \<Longrightarrow> idx \<le> max from to \<Longrightarrow>
              trace_assms t \<Longrightarrow>
              traces_enabled (body idx vars) (run s t)"
    and "\<And>idx vars t t' vars'.
              Inv idx vars (run s t) \<Longrightarrow>
              min from to \<le> min idx (idx + step) \<Longrightarrow> max idx (idx + step) \<le> max from to \<Longrightarrow>
              Run (body idx vars) t' vars' \<Longrightarrow> trace_assms t \<Longrightarrow> trace_assms t' \<Longrightarrow>
              Inv (idx + step) vars' (run (run s t) t')"
    and "(step > 0 \<and> from \<le> to) \<or> (step < 0 \<and> from \<ge> to) \<Longrightarrow> Inv from vars s"
  shows "traces_enabled (foreachM (index_list from to step) vars body) s"
proof (use assms in \<open>induction "from" to step arbitrary: vars s rule: index_list.induct[case_names Step]\<close>)
  case (Step "from" to step vars s)
  note body = Step.prems(1)
  note Inv_step = Step.prems(2)
  note Inv_base = Step.prems(3)
  have "traces_enabled (body from vars \<bind> (\<lambda>vars'. foreachM (index_list (from + step) to step) vars' body)) s"
    if "0 < step \<and> from \<le> to \<or> step < 0 \<and> to \<le> from"
  proof (rule traces_enabled_bind)
    show "traces_enabled (body from vars) s"
      using body[of "from" vars "[]"] Inv_base[OF that]
      by auto
  next
    fix t vars'
    assume t: "Run (body from vars) t vars'" "trace_assms t"
    note body' = body[of _ _ "t @ t'" for t', simplified]
    note Inv_step' = Inv_step[of _ _ "t @ t'" t'' for t' t'', simplified]
    note Inv_base' = Inv_step[of "from" vars "[]" t vars', simplified]
    have "traces_enabled (foreachM (index_list (from + step) to step) vars' body) (run s t)"
      if "0 < step \<and> from + step \<le> to \<or> step < 0 \<and> to \<le> from + step"
      using that Inv_base t
      by (intro Step.IH) (auto intro: body' Inv_step' Inv_base')
    then show "traces_enabled (foreachM (index_list (from + step) to step) vars' body) (run s t)"
      unfolding index_list.simps[of "from + step" to step]
      by (auto intro: non_cap_exp_return[THEN non_cap_exp_traces_enabledI])
  qed
  then show ?case
    unfolding index_list.simps[of "from" to step]
    by (auto intro: non_cap_exp_return[THEN non_cap_exp_traces_enabledI])
qed

lemma traces_enabled_foreachM_index_list_inv2:
  assumes "\<And>idx var_a var_b t.
              Inv idx var_a var_b (run s t) \<Longrightarrow>
              min from to \<le> idx \<Longrightarrow> idx \<le> max from to \<Longrightarrow>
              trace_assms t \<Longrightarrow>
              traces_enabled (body idx (var_a, var_b)) (run s t)"
    and "\<And>idx var_a var_b t t' var_a' var_b'.
              Inv idx var_a var_b (run s t) \<Longrightarrow>
              min from to \<le> min idx (idx + step) \<Longrightarrow> max idx (idx + step) \<le> max from to \<Longrightarrow>
              Run (body idx (var_a, var_b)) t' (var_a', var_b') \<Longrightarrow> trace_assms t \<Longrightarrow> trace_assms t' \<Longrightarrow>
              Inv (idx + step) var_a' var_b' (run (run s t) t')"
    and "(step > 0 \<and> from \<le> to) \<or> (step < 0 \<and> from \<ge> to) \<Longrightarrow> Inv from var_a var_b s"
  shows "traces_enabled (foreachM (index_list from to step) (var_a, var_b) body) s"
  using assms
  by (intro traces_enabled_foreachM_index_list_inv[where Inv = "\<lambda>idx vars s. case vars of (var_a, var_b) \<Rightarrow> Inv idx var_a var_b s"]) auto

lemma traces_enabled_foreachM_index_list_inv3:
  assumes "\<And>idx var_a var_b var_c t.
              Inv idx var_a var_b var_c (run s t) \<Longrightarrow>
              min from to \<le> idx \<Longrightarrow> idx \<le> max from to \<Longrightarrow>
              trace_assms t \<Longrightarrow>
              traces_enabled (body idx (var_a, var_b, var_c)) (run s t)"
    and "\<And>idx var_a var_b var_c t t' var_a' var_b' var_c'.
              Inv idx var_a var_b var_c (run s t) \<Longrightarrow>
              min from to \<le> min idx (idx + step) \<Longrightarrow> max idx (idx + step) \<le> max from to \<Longrightarrow>
              Run (body idx (var_a, var_b, var_c)) t' (var_a', var_b', var_c') \<Longrightarrow> trace_assms t \<Longrightarrow> trace_assms t' \<Longrightarrow>
              Inv (idx + step) var_a' var_b' var_c' (run (run s t) t')"
    and "(step > 0 \<and> from \<le> to) \<or> (step < 0 \<and> from \<ge> to) \<Longrightarrow> Inv from var_a var_b var_c s"
  shows "traces_enabled (foreachM (index_list from to step) (var_a, var_b, var_c) body) s"
  using assms
  by (intro traces_enabled_foreachM_index_list_inv2[where Inv = "\<lambda>idx var_a vars s. case vars of (var_b, var_c) \<Rightarrow> Inv idx var_a var_b var_c s"]) auto

lemma traces_enabled_foreachM_inv:
  assumes "\<And>x vars t. Inv vars (run s t) \<Longrightarrow> x \<in> set xs \<Longrightarrow> traces_enabled (body x vars) (run s t)"
    and "\<And>x vars t t' vars'. Inv vars (run s t) \<Longrightarrow> x \<in> set xs \<Longrightarrow> Run (body x vars) t' vars' \<Longrightarrow> trace_assms t' \<Longrightarrow> Inv vars' (run (run s t) t')"
    and "Inv vars s"
  shows "traces_enabled (foreachM xs vars body) s"
proof (use assms in \<open>induction xs arbitrary: vars s\<close>)
  case (Cons x xs vars s)
  note body = Cons.prems(1)
  note Inv_step = Cons.prems(2)
  note Inv_base = Cons.prems(3)
  have "traces_enabled (body x vars \<bind> (\<lambda>vars'. foreachM xs vars' body)) s"
  proof (rule traces_enabled_bind)
    show "traces_enabled (body x vars) s"
      using body[of vars "[]" x] Inv_base
      by auto
  next
    fix t vars'
    assume t: "Run (body x vars) t vars'" "trace_assms t"
    note body' = body[of _ "t @ t'" for t', simplified]
    note Inv_step' = Inv_step[of _ "t @ t'" for t', simplified]
    note Inv_base' = Inv_step[of vars "[]" x t vars', simplified]
    show "traces_enabled (foreachM xs vars' body) (run s t)"
      using t Inv_base
      by (intro Cons.IH) (auto intro: body' Inv_step' Inv_base')
  qed
  then show "traces_enabled (foreachM (x # xs) vars body) s"
    by auto
qed (auto intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_foreachM_accessible_regs:
  assumes "Rs \<subseteq> accessible_regs s0" and "Rs \<subseteq> accessible_regs s0 \<Longrightarrow> Rs \<subseteq> accessible_regs s"
    and "\<And>x vars. x \<in> set xs \<Longrightarrow> runs_no_reg_writes_to (Rs \<inter> (PCC ISA \<union> IDC ISA)) (body x vars)"
    and "\<And>x vars t. Rs \<subseteq> accessible_regs (run s t) \<Longrightarrow> x \<in> set xs \<Longrightarrow> traces_enabled (body x vars) (run s t)"
  shows "traces_enabled (foreachM xs vars body) s"
  using assms
proof (intro traces_enabled_foreachM_inv[where Inv = "\<lambda>vars s. Rs \<subseteq> accessible_regs s"])
  fix x vars s t vars'
  assume "Rs \<subseteq> accessible_regs s" and "x \<in> set xs" and "Run (body x vars) t vars'"
  then show "Rs \<subseteq> accessible_regs (run s t)"
    by (elim accessible_regs_no_writes_run_subset) (auto intro: assms)
qed (use assms in auto)

lemma traces_enabled_foreachM:
  assumes "\<And>x vars t. x \<in> set xs \<Longrightarrow> trace_assms t \<Longrightarrow> traces_enabled (body x vars) (run s t)"
  shows "traces_enabled (foreachM xs vars body) s"
proof (intro traces_enabled_foreachM_inv[where Inv = "\<lambda>vars s'. \<exists>t. s' = run s t \<and> trace_assms t"])
  fix x vars s'
  assume "\<exists>t. s' = run s t \<and> trace_assms t" and "x \<in> set xs"
  then show "traces_enabled (body x vars) s'"
    using assms
    by auto
next
  fix x vars s' t vars'
  assume P: "\<exists>t. s' = run s t \<and> trace_assms t" and x: "x \<in> set xs"
    and t: "Run (body x vars) t vars'" "trace_assms t"
  from P obtain t' where "s' = run s t'" and "trace_assms t'"
    by auto
  then have "run s' t = run s (t' @ t)" and "trace_assms (t' @ t)"
    using t
    by auto
  then show "\<exists>t'. run s' t = run s t' \<and> trace_assms t'"
    by blast
next
  have "s = run s []" and "trace_assms []"
    by auto
  then show "\<exists>t. s = run s t \<and> trace_assms t"
    by blast
qed

lemma traces_enabled_try_catch:
  assumes "traces_enabled m s"
    and "\<And>tm e th m'.
           \<lbrakk>(m, tm, Exception e) \<in> Traces; (h e, th, m') \<in> Traces; finished m'; trace_assms tm\<rbrakk> \<Longrightarrow>
           trace_enabled s (tm @ th)"
  shows "traces_enabled (try_catch m h) s"
proof -
  have *: "finished (try_catch m h) \<longleftrightarrow> (\<exists>a. m = Done a) \<or> (\<exists>msg. m = Fail msg \<and> finished m) \<or> (\<exists>e. m = Exception e \<and> (h e, [], h e) \<in> Traces \<and> finished (h e))" for m
    by (cases m) (auto simp: finished_def isException_def)
  show ?thesis
    using assms
    by (fastforce simp: traces_enabled_def trace_enabled_append_iff * elim!: try_catch_Traces_cases)
qed

lemma traces_enabled_liftR[traces_enabledI]:
  assumes "traces_enabled m s"
  shows "traces_enabled (liftR m) s"
  using assms
  unfolding liftR_def
  by (intro traces_enabled_try_catch) (auto simp: traces_enabled_def)

definition
  "early_returns_enabled m s \<equiv>
     traces_enabled m s \<and>
     (\<forall>t a. (m, t, Exception (Inl a)) \<in> Traces \<and> trace_assms t \<longrightarrow> trace_enabled s t)"

lemma traces_enabled_catch_early_return[traces_enabledI]:
  assumes "early_returns_enabled m s"
  shows "traces_enabled (catch_early_return m) s"
  using assms
  unfolding catch_early_return_def
  by (intro traces_enabled_try_catch)
     (auto simp: traces_enabled_def early_returns_enabled_def split: sum.splits)

lemma liftR_no_early_return[simp]:
  shows "(liftR m, t, Exception (Inl e)) \<in> Traces \<longleftrightarrow> False"
  by (induction m arbitrary: t) (auto simp: liftR_def elim: Traces_cases)

lemma early_returns_enabled_liftR[traces_enabledI]:
  assumes "traces_enabled m s"
  shows "early_returns_enabled (liftR m) s"
  using assms
  by (auto simp: early_returns_enabled_def intro: traces_enabled_liftR)

lemma early_returns_enabled_return[traces_enabledI]:
  "early_returns_enabled (return a) s"
  by (auto simp: early_returns_enabled_def traces_enabled_def)

lemma early_returns_enabled_bind[traces_enabledI]:
  assumes m: "early_returns_enabled m s"
    and f: "\<And>t a. Run m t a \<Longrightarrow> trace_assms t \<Longrightarrow> early_returns_enabled (f a) (run s t)"
  shows "early_returns_enabled (m \<bind> f) s"
proof -
  { fix t a
    assume "(m \<bind> f, t, Exception (Inl a)) \<in> Traces" and t: "trace_assms t"
    then have "trace_enabled s t"
    proof (cases rule: bind_Traces_cases)
      case (Left m'')
      then consider "m'' = Exception (Inl a)" | a' where "m'' = Done a'" and "f a' = Exception (Inl a)"
        by (cases m'') auto
      then show ?thesis
        using Left m t
        by cases (auto simp: early_returns_enabled_def traces_enabled_def)
    next
      case (Bind tm am tf)
      then show ?thesis
        using Bind m f[of tm am] t
        by (auto simp: trace_enabled_append_iff early_returns_enabled_def traces_enabled_def)
    qed
  }
  then show ?thesis
    using assms
    by (auto intro: traces_enabled_bind simp: early_returns_enabled_def)
qed

lemma early_returns_enabled_early_return[traces_enabledI]:
  "early_returns_enabled (early_return a) s"
  by (auto simp: early_returns_enabled_def early_return_def throw_def traces_enabled_def)

lemma early_returns_enabled_let[traces_enabledI]:
  assumes "early_returns_enabled (f y) s"
  shows "early_returns_enabled (let x = y in f x) s"
  using assms
  by auto

lemma early_returns_enabled_case_prod[traces_enabledI]:
  assumes "\<And>x y. z = (x, y) \<Longrightarrow> early_returns_enabled (f x y) s"
  shows "early_returns_enabled (case z of (x, y) \<Rightarrow> f x y) s"
  using assms
  by auto

lemma early_returns_enabled_if[traces_enabledI]:
  assumes "c \<Longrightarrow> early_returns_enabled m1 s" and "\<not>c \<Longrightarrow> early_returns_enabled m2 s"
  shows "early_returns_enabled (if c then m1 else m2) s"
  using assms
  by auto

lemma early_returns_enabled_if_ignore_cond:
  assumes "early_returns_enabled m1 s" and "early_returns_enabled m2 s"
  shows "early_returns_enabled (if c then m1 else m2) s"
  using assms
  by auto

lemma early_returns_enabled_and_boolM[traces_enabledI]:
  assumes "early_returns_enabled m1 s"
    and "\<And>t. Run m1 t True \<Longrightarrow> early_returns_enabled m2 (run s t)"
  shows "early_returns_enabled (and_boolM m1 m2) s"
  using assms
  by (auto simp: and_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma early_returns_enabled_or_boolM[traces_enabledI]:
  assumes "early_returns_enabled m1 s"
    and "\<And>t. Run m1 t False \<Longrightarrow> early_returns_enabled m2 (run s t)"
  shows "early_returns_enabled (or_boolM m1 m2) s"
  using assms
  by (auto simp: or_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma early_returns_enabled_foreachM_inv:
  assumes "\<And>x vars s. P vars s \<Longrightarrow> x \<in> set xs \<Longrightarrow> early_returns_enabled (body x vars) s"
    and "\<And>x vars s t vars'. P vars s \<Longrightarrow> x \<in> set xs \<Longrightarrow> Run (body x vars) t vars' \<Longrightarrow> P vars' (run s t)"
    and "P vars s"
  shows "early_returns_enabled (foreachM xs vars body) s"
  by (use assms in \<open>induction xs arbitrary: vars s\<close>;
      fastforce intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma non_cap_exp_Run_inv_traces_enabled_runE:
  assumes "Run m1 t a" and "non_cap_exp m1" and "traces_enabled m2 s"
  shows "traces_enabled m2 (run s t)"
  using assms
  by (auto simp: non_cap_exp_Run_run_invI)

lemma non_cap_exp_Run_inv_early_returns_enabled_runE:
  assumes "Run m1 t a" and "non_cap_exp m1" and "early_returns_enabled m2 s"
  shows "early_returns_enabled m2 (run s t)"
  using assms
  by (auto simp: non_cap_exp_Run_run_invI)

method try_simp_traces_enabled =
  ((match conclusion in \<open>traces_enabled m2 (run s t)\<close> for m2 s t \<Rightarrow>
     \<open>match premises in m1: \<open>Run m1 t a\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_traces_enabled_runE[OF m1], solves \<open>non_cap_expI_base\<close>)?\<close>\<close>
   \<bar> \<open>early_returns_enabled m2 (run s t)\<close> for m2 s t \<Rightarrow>
     \<open>match premises in m1: \<open>Run m1 t a\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_early_returns_enabled_runE[OF m1], solves \<open>non_cap_expI_base\<close>)?\<close>\<close>)?)

named_theorems traces_enabled_combinatorI

lemmas traces_enabled_builtin_combinatorsI =
  traces_enabled_bind traces_enabled_and_boolM traces_enabled_or_boolM
  early_returns_enabled_bind early_returns_enabled_and_boolM early_returns_enabled_or_boolM

named_theorems traces_enabled_split
declare option.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare prod.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare sum.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare bool.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

method traces_enabled_foreachM_intro uses assms simp =
  (match conclusion in \<open>traces_enabled (foreachM _ _ _) _\<close> \<Rightarrow>
     \<open>match assms in Rs_acc: \<open>Rs \<subseteq> accessible_regs _\<close> for Rs \<Rightarrow>
        \<open>(rule traces_enabled_foreachM_accessible_regs[OF Rs_acc],
          solves \<open>accessible_regsI\<close>,
          solves \<open>no_reg_writes_toI simp: simp\<close>)\<close>\<close>
   | (rule traces_enabled_foreachM))

method traces_enabled_step uses simp intro elim assms =
  ((rule intro allI impI conjI)
    | (erule elim conjE)
    | ((rule traces_enabled_combinatorI traces_enabled_builtin_combinatorsI[rotated], try_simp_traces_enabled))
    | (rule traces_enabledI TrueI)
    | (rule traces_enabled_split[THEN iffD2]; intro allI conjI impI)
    | (traces_enabled_foreachM_intro assms: assms simp: simp)
    | (rule insert_subset[where B="insert y C" for y C, THEN iffD2], simp(no_asm)))

method traces_enabledI_with methods solve uses intro elim =
  ((rule intro TrueI; traces_enabledI_with solve intro: intro elim: elim)
    | (erule elim conjE; traces_enabledI_with solve intro: intro elim: elim)
    | ((rule traces_enabled_combinatorI traces_enabled_builtin_combinatorsI[rotated], try_simp_traces_enabled); traces_enabledI_with solve intro: intro elim: elim)
    | (rule traces_enabledI; traces_enabledI_with solve intro: intro elim: elim)
    | (rule traces_enabled_split[THEN iffD2]; intro conjI impI; traces_enabledI_with solve intro: intro elim: elim)
    | solve)

(*method traces_enabledI uses simp intro elim assms =
  (traces_enabledI_with
     \<open>(solves \<open>accessible_regsI simp: simp assms: assms\<close>)
      | (solves \<open>derivable_capsI simp: simp assms: assms\<close>)
      | (use assms in \<open>auto intro!: intro elim!: elim simp: simp\<close>)?\<close>
     intro: intro)*)

method traces_enabledI uses simp intro elim assms =
  (((traces_enabled_step simp: simp intro: intro elim: elim assms: assms)+; traces_enabledI simp: simp intro: intro elim: elim assms: assms)
    | (accessible_regs_step simp: simp assms: assms; solves \<open>traces_enabledI simp: simp intro: intro elim: elim assms: assms\<close>)
    | (derivable_caps_step; solves \<open>traces_enabledI simp: simp intro: intro elim: elim assms: assms\<close>)
    | (solves \<open>no_reg_writes_toI simp: simp\<close>)
    | (use assms in \<open>auto intro!: intro elim!: elim simp: simp\<close>)?)

(* method traces_enabledI = (intro traces_enabledI preserves_invariantI) *)

lemma if_derivable_capsI[derivable_capsI]:
  assumes "cond \<Longrightarrow> c1 \<in> derivable_caps s" and "\<not>cond \<Longrightarrow> c2 \<in> derivable_caps s"
  shows "(if cond then c1 else c2) \<in> derivable_caps s"
  using assms
  by auto


end

locale Cap_Axiom_Inv_Automaton = Cap_Axiom_Automaton CC ISA enabled use_mem_caps +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool"
    and use_mem_caps :: bool
    and get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
    and invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set" +
  fixes ex_traces :: bool
  assumes non_cap_event_enabled: "\<And>e. non_cap_event e \<Longrightarrow> enabled s e"
    and read_non_special_regs_enabled: "\<And>r v. r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<Longrightarrow> enabled s (E_read_reg r v)"
begin

definition "isException m \<equiv> ((\<exists>e. m = Exception e) \<or> (\<exists>msg. m = Fail msg)) \<and> ex_traces"

definition finished :: "('regval,'a,'ex) monad \<Rightarrow> bool" where
  "finished m = ((\<exists>a. m = Done a) \<or> isException m)"

lemma finishedE:
  assumes "finished m"
  obtains (Done) a where "m = Done a"
  | (Ex) "isException m"
  using assms
  by (auto simp: finished_def)

lemma finished_cases:
  assumes "finished m"
  obtains (Done) a where "m = Done a" | (Fail) msg where "m = Fail msg" | (Ex) e where "m = Exception e"
  using assms
  by (auto simp: finished_def isException_def)

lemma finished_Done[intro, simp]:
  "finished (Done a)"
  by (auto simp: finished_def)

lemma finished_Fail[intro, simp]:
  "finished (Fail msg) \<Longrightarrow> finished (Fail msg')"
  unfolding finished_def isException_def
  by auto

lemma finished_Exception[intro, simp]:
  "finished (Exception e) \<Longrightarrow> finished (Exception e')"
  unfolding finished_def isException_def
  by auto

lemma finished_isException[intro, simp]:
  "isException m \<Longrightarrow> finished m"
  by (auto simp: finished_def)

lemma finished_bind_left:
  assumes "finished (m \<bind> f)"
  shows "finished m"
  using assms
  unfolding finished_def isException_def
  by (cases m) auto

definition
  "traces_enabled m s regs \<equiv>
     \<forall>t m'. (m, t, m') \<in> Traces \<and> finished m' \<and> reads_regs_from inv_regs t regs \<and> invariant regs \<longrightarrow> trace_enabled s t"

lemma traces_enabled_accepts_fromI:
  assumes "hasTrace t m" and "traces_enabled m s regs" and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
    and "reads_regs_from inv_regs t regs" and "invariant regs"
  shows "accepts_from s t"
  using assms
  unfolding traces_enabled_def finished_def isException_def
  unfolding hasTrace_iff_Traces_final hasException_iff_Traces_Exception hasFailure_iff_Traces_Fail
  unfolding runTrace_iff_Traces[symmetric]
  by (intro trace_enabled_acceptI) (auto elim!: final_cases)

named_theorems traces_enabledI

lemma traces_enabled_bind[traces_enabledI]:
  assumes "runs_preserve_invariant m" and "traces_enabled m s regs"
    and "\<And>t a. Run_inv m t a regs \<Longrightarrow> traces_enabled (f a) (run s t) (the (updates_regs inv_regs t regs))"
  shows "traces_enabled (m \<bind> f) s regs"
  using assms
  by (auto simp: traces_enabled_def Run_inv_def regstate_simp trace_enabled_append_iff
           dest!: finished_bind_left elim!: bind_Traces_cases elim!: runs_preserve_invariantE; fastforce)

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabled non_cap_event_axiom_step_inv)

lemma non_cap_exp_trace_enabledI:
  assumes m: "non_cap_exp m"
    and t: "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF m t])
     (auto intro: non_cap_trace_enabledI read_non_special_regs_enabled simp: trace_enabled_append_iff)

lemma non_cap_exp_traces_enabledI:
  assumes "non_cap_exp m"
  shows "traces_enabled m s regs"
  using assms
  by (auto simp: traces_enabled_def intro: non_cap_exp_trace_enabledI)

lemma Run_inv_RunI[simp]: "Run_inv m t a regs \<Longrightarrow> Run m t a"
  by (simp add: Run_inv_def)

lemma traces_enabled_let[traces_enabledI]:
  assumes "traces_enabled (f y) s regs"
  shows "traces_enabled (let x = y in f x) s regs"
  using assms
  by auto

lemma traces_enabled_case_prod[traces_enabledI]:
  assumes "\<And>x y. z = (x, y) \<Longrightarrow> traces_enabled (f x y) s regs"
  shows "traces_enabled (case z of (x, y) \<Rightarrow> f x y) s regs"
  using assms
  by auto

lemma traces_enabled_if[traces_enabledI]:
  assumes "c \<Longrightarrow> traces_enabled m1 s regs" and "\<not>c \<Longrightarrow> traces_enabled m2 s regs"
  shows "traces_enabled (if c then m1 else m2) s regs"
  using assms
  by auto

lemma traces_enabled_if_ignore_cond:
  assumes "traces_enabled m1 s regs" and "traces_enabled m2 s regs"
  shows "traces_enabled (if c then m1 else m2) s regs"
  using assms
  by auto

lemma traces_enabled_and_boolM[traces_enabledI]:
  assumes "runs_preserve_invariant m1" and "traces_enabled m1 s regs"
    and "\<And>t. Run_inv m1 t True regs \<Longrightarrow> traces_enabled m2 (run s t) (the (updates_regs inv_regs t regs))"
  shows "traces_enabled (and_boolM m1 m2) s regs"
  using assms
  by (auto simp: and_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_or_boolM[traces_enabledI]:
  assumes "runs_preserve_invariant m1" and "traces_enabled m1 s regs"
    and "\<And>t. Run_inv m1 t False regs \<Longrightarrow> traces_enabled m2 (run s t) (the (updates_regs inv_regs t regs))"
  shows "traces_enabled (or_boolM m1 m2) s regs"
  using assms
  by (auto simp: or_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_foreachM_inv:
  assumes "\<And>x vars s regs. P vars s regs \<Longrightarrow> x \<in> set xs \<Longrightarrow> traces_enabled (body x vars) s regs"
    and "\<And>x vars. x \<in> set xs \<Longrightarrow> runs_preserve_invariant (body x vars)"
    and "\<And>x vars s regs t vars'. P vars s regs \<Longrightarrow> x \<in> set xs \<Longrightarrow> Run_inv (body x vars) t vars' regs \<Longrightarrow> P vars' (run s t) (the (updates_regs inv_regs t regs))"
    and "P vars s regs"
  shows "traces_enabled (foreachM xs vars body) s regs"
  by (use assms in \<open>induction xs arbitrary: vars s regs\<close>;
      fastforce intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma traces_enabled_try_catch:
  assumes "traces_enabled m s regs"
    and "\<And>tm e th m'.
           (m, tm, Exception e) \<in> Traces \<Longrightarrow> (h e, th, m') \<in> Traces \<Longrightarrow> finished m' \<Longrightarrow>
           reads_regs_from inv_regs (tm @ th) regs \<Longrightarrow> invariant regs \<Longrightarrow>
           trace_enabled s (tm @ th)"
  shows "traces_enabled (try_catch m h) s regs"
proof -
  (* have *: "isException (try_catch m h) \<longleftrightarrow> (\<exists>em eh. m = Exception em \<and> h em = Exception eh \<and> finished (Exception eh :: ('regval, 'a, 'c) monad))" for m *)
  (*have *: "isException (try_catch m h) \<longleftrightarrow> (\<exists>msg. m = Fail msg \<and> finished (Fail msg :: ('regval, 'a, 'b) monad)) \<or> (\<exists>em eh. m = Exception em \<and> isException (h em))" for m
    unfolding isException_def finished_def
    by (cases m) auto
  have **: "try_catch m h = Done a \<longleftrightarrow> m = Done a \<or> (\<exists>e. m = Exception e \<and> h e = Done a)" for a m
    by (cases m) auto
  have ***: "try_catch m h = Fail msg \<longleftrightarrow> m = Fail msg \<or> (\<exists>e. m = Exception e \<and> h e = Fail msg)" for msg m
    by (cases m) auto*)
  have *: "finished (try_catch m h) \<longleftrightarrow> (\<exists>a. m = Done a) \<or> (\<exists>msg. m = Fail msg \<and> finished m) \<or> (\<exists>e. m = Exception e \<and> (h e, [], h e) \<in> Traces \<and> finished (h e))" for m
    by (cases m) (auto simp: finished_def isException_def)
  show ?thesis
    using assms
    by (fastforce simp: traces_enabled_def regstate_simp trace_enabled_append_iff Run_inv_def *
             elim!: try_catch_Traces_cases elim: traces_preserve_invariantE)
qed

lemma traces_enabled_liftR[traces_enabledI]:
  assumes "traces_enabled m s regs"
  shows "traces_enabled (liftR m) s regs"
  using assms
  unfolding liftR_def
  by (intro traces_enabled_try_catch) (auto simp: traces_enabled_def Run_inv_def)

definition
  "early_returns_enabled m s regs \<equiv>
     traces_enabled m s regs \<and>
     (\<forall>t a. (m, t, Exception (Inl a)) \<in> Traces \<and> reads_regs_from inv_regs t regs \<and> invariant regs \<longrightarrow> trace_enabled s t)"

lemma traces_enabled_catch_early_return[traces_enabledI]:
  assumes "early_returns_enabled m s regs"
  shows "traces_enabled (catch_early_return m) s regs"
  using assms
  unfolding catch_early_return_def
  by (intro traces_enabled_try_catch)
     (auto simp: traces_enabled_def early_returns_enabled_def Run_inv_def split: sum.splits)

lemma liftR_no_early_return[simp]:
  shows "(liftR m, t, Exception (Inl e)) \<in> Traces \<longleftrightarrow> False"
  by (induction m arbitrary: t) (auto simp: liftR_def elim: Traces_cases)

lemma early_returns_enabled_liftR[traces_enabledI]:
  assumes "traces_enabled m s regs"
  shows "early_returns_enabled (liftR m) s regs"
  using assms
  by (auto simp: early_returns_enabled_def intro: traces_enabled_liftR)

lemma early_returns_enabled_return[traces_enabledI]:
  "early_returns_enabled (return a) s regs"
  by (auto simp: early_returns_enabled_def traces_enabled_def)

lemma early_returns_enabled_bind[traces_enabledI]:
  assumes inv: "traces_preserve_invariant m"
    and m: "early_returns_enabled m s regs"
    and f: "\<And>t a. Run_inv m t a regs \<Longrightarrow> early_returns_enabled (f a) (run s t) (the (updates_regs inv_regs t regs))"
  shows "early_returns_enabled (m \<bind> f) s regs"
proof -
  { fix t a
    assume "(m \<bind> f, t, Exception (Inl a)) \<in> Traces" and t: "reads_regs_from inv_regs t regs" and regs: "invariant regs"
    then have "trace_enabled s t"
    proof (cases rule: bind_Traces_cases)
      case (Left m'')
      then consider "m'' = Exception (Inl a)" | a' where "m'' = Done a'" and "f a' = Exception (Inl a)"
        by (cases m'') auto
      then show ?thesis
        using Left m t regs
        by cases (auto simp: early_returns_enabled_def traces_enabled_def)
    next
      case (Bind tm am tf)
      then obtain regs'
        where "updates_regs inv_regs tm regs = Some regs'" and "invariant regs'"
          and "reads_regs_from inv_regs tm regs" and "reads_regs_from inv_regs tf regs'"
        using t regs
        by (elim traces_preserve_invariantE[OF inv]) (auto simp: regstate_simp)
      then show ?thesis
        using Bind m f[of tm am] regs
        by (auto simp: trace_enabled_append_iff early_returns_enabled_def traces_enabled_def Run_inv_def)
    qed
  }
  then show ?thesis
    using assms
    by (auto intro: traces_enabled_bind traces_runs_preserve_invariantI simp: early_returns_enabled_def)
qed

lemma early_returns_enabled_early_return[traces_enabledI]:
  "early_returns_enabled (early_return a) s regs"
  by (auto simp: early_returns_enabled_def early_return_def throw_def traces_enabled_def)

lemma early_returns_enabled_let[traces_enabledI]:
  assumes "early_returns_enabled (f y) s regs"
  shows "early_returns_enabled (let x = y in f x) s regs"
  using assms
  by auto

lemma early_returns_enabled_case_prod[traces_enabledI]:
  assumes "\<And>x y. z = (x, y) \<Longrightarrow> early_returns_enabled (f x y) s regs"
  shows "early_returns_enabled (case z of (x, y) \<Rightarrow> f x y) s regs"
  using assms
  by auto

lemma early_returns_enabled_if[traces_enabledI]:
  assumes "c \<Longrightarrow> early_returns_enabled m1 s regs" and "\<not>c \<Longrightarrow> early_returns_enabled m2 s regs"
  shows "early_returns_enabled (if c then m1 else m2) s regs"
  using assms
  by auto

lemma early_returns_enabled_if_ignore_cond:
  assumes "early_returns_enabled m1 s regs" and "early_returns_enabled m2 s regs"
  shows "early_returns_enabled (if c then m1 else m2) s regs"
  using assms
  by auto

lemma early_returns_enabled_and_boolM[traces_enabledI]:
  assumes "traces_preserve_invariant m1" and "early_returns_enabled m1 s regs"
    and "\<And>t. Run_inv m1 t True regs \<Longrightarrow> early_returns_enabled m2 (run s t) (the (updates_regs inv_regs t regs))"
  shows "early_returns_enabled (and_boolM m1 m2) s regs"
  using assms
  by (auto simp: and_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma early_returns_enabled_or_boolM[traces_enabledI]:
  assumes "traces_preserve_invariant m1" and "early_returns_enabled m1 s regs"
    and "\<And>t. Run_inv m1 t False regs \<Longrightarrow> early_returns_enabled m2 (run s t) (the (updates_regs inv_regs t regs))"
  shows "early_returns_enabled (or_boolM m1 m2) s regs"
  using assms
  by (auto simp: or_boolM_def intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma early_returns_enabled_foreachM_inv:
  assumes "\<And>x vars s regs. P vars s regs \<Longrightarrow> x \<in> set xs \<Longrightarrow> early_returns_enabled (body x vars) s regs"
    and "\<And>x vars. x \<in> set xs \<Longrightarrow> traces_preserve_invariant (body x vars)"
    and "\<And>x vars s regs t vars'. P vars s regs \<Longrightarrow> x \<in> set xs \<Longrightarrow> Run_inv (body x vars) t vars' regs \<Longrightarrow> P vars' (run s t) (the (updates_regs inv_regs t regs))"
    and "P vars s regs"
  shows "early_returns_enabled (foreachM xs vars body) s regs"
  by (use assms in \<open>induction xs arbitrary: vars s regs\<close>;
      fastforce intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

lemma non_cap_exp_Run_inv_traces_enabled_runE:
  assumes "Run_inv m1 t a regs" and "non_cap_exp m1" and "traces_enabled m2 s regs'"
  shows "traces_enabled m2 (run s t) regs'"
  using assms
  by (auto simp: Run_inv_def non_cap_exp_Run_run_invI)

lemma no_reg_writes_Run_inv_traces_enabled_updates_regsE:
  assumes "Run_inv m1 t a regs" and "no_reg_writes_to inv_regs m1" and "traces_enabled m2 s regs"
  shows "traces_enabled m2 s (the (updates_regs inv_regs t regs))"
  using assms
  by (auto simp: Run_inv_def)

lemma non_cap_exp_Run_inv_early_returns_enabled_runE:
  assumes "Run_inv m1 t a regs" and "non_cap_exp m1" and "early_returns_enabled m2 s regs'"
  shows "early_returns_enabled m2 (run s t) regs'"
  using assms
  by (auto simp: Run_inv_def non_cap_exp_Run_run_invI)

lemma no_reg_writes_Run_inv_early_returns_enabled_updates_regsE:
  assumes "Run_inv m1 t a regs" and "no_reg_writes_to inv_regs m1" and "early_returns_enabled m2 s regs"
  shows "early_returns_enabled m2 s (the (updates_regs inv_regs t regs))"
  using assms
  by (auto simp: Run_inv_def)

method try_simp_traces_enabled =
  ((match conclusion in \<open>traces_enabled m2 (run s t) (the (updates_regs inv_regs t regs))\<close> for m2 s t regs \<Rightarrow>
     \<open>match premises in m1: \<open>Run_inv m1 t a regs\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_traces_enabled_runE[OF m1], solves \<open>non_cap_expI\<close>)?,
         (rule no_reg_writes_Run_inv_traces_enabled_updates_regsE[OF m1], solves \<open>no_reg_writes_toI\<close>)?\<close>\<close>
   \<bar> \<open>early_returns_enabled m2 (run s t) (the (updates_regs inv_regs t regs))\<close> for m2 s t regs \<Rightarrow>
     \<open>match premises in m1: \<open>Run_inv m1 t a regs\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_early_returns_enabled_runE[OF m1], solves \<open>non_cap_expI\<close>)?,
         (rule no_reg_writes_Run_inv_early_returns_enabled_updates_regsE[OF m1], solves \<open>no_reg_writes_toI\<close>)?\<close>\<close>)?)

named_theorems traces_enabled_combinatorI

lemmas traces_enabled_builtin_combinatorsI =
  traces_enabled_bind traces_enabled_and_boolM traces_enabled_or_boolM
  early_returns_enabled_bind early_returns_enabled_and_boolM early_returns_enabled_or_boolM

named_theorems traces_enabled_split
declare option.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare prod.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare sum.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare bool.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]

method traces_enabled_step uses intro elim =
  ((rule intro TrueI)
    | (erule elim eqTrueE)
    | ((rule traces_enabled_combinatorI traces_enabled_builtin_combinatorsI[rotated 2], try_simp_traces_enabled))
    | (rule traces_enabledI preserves_invariantI)
    | (rule traces_enabled_split[THEN iffD2]; intro allI conjI impI))

method traces_enabledI_with methods solve uses intro elim =
  ((rule intro TrueI; traces_enabledI_with solve intro: intro elim: elim)
    | (erule elim eqTrueE; traces_enabledI_with solve intro: intro elim: elim)
    | ((rule traces_enabled_combinatorI traces_enabled_builtin_combinatorsI[rotated 2], try_simp_traces_enabled); traces_enabledI_with solve intro: intro elim: elim)
    | (rule traces_enabledI; traces_enabledI_with solve intro: intro elim: elim)
    | (preserves_invariantI intro: intro elim: elim; traces_enabledI_with solve intro: intro elim: elim)
    | (rule traces_enabled_split[THEN iffD2]; intro conjI impI; traces_enabledI_with solve intro: intro elim: elim)
    | solve)

(*method traces_enabledI uses simp intro elim assms =
  (traces_enabledI_with
     \<open>(solves \<open>accessible_regsI simp: simp assms: assms\<close>)
      | (solves \<open>derivable_capsI simp: simp assms: assms\<close>)
      | (use assms in \<open>auto intro!: intro elim!: elim simp: simp\<close>)?\<close>
     intro: intro)*)

method traces_enabledI uses simp intro elim assms =
  ((traces_enabled_step intro: intro elim: elim; traces_enabledI simp: simp intro: intro elim: elim assms: assms)+
    | (accessible_regs_step simp: simp assms: assms; solves \<open>traces_enabledI simp: simp intro: intro elim: elim assms: assms\<close>)
    | (derivable_caps_step; solves \<open>traces_enabledI simp: simp intro: intro elim: elim assms: assms\<close>)
    | (solves \<open>no_reg_writes_toI simp: simp\<close>)
    | (solves \<open>preserves_invariantI simp: simp\<close>)
    | (use assms in \<open>auto intro!: intro elim!: elim simp: simp\<close>)?)

(* method traces_enabledI = (intro traces_enabledI preserves_invariantI) *)

lemma if_derivable_capsI[derivable_capsI]:
  assumes "cond \<Longrightarrow> c1 \<in> derivable_caps s" and "\<not>cond \<Longrightarrow> c2 \<in> derivable_caps s"
  shows "(if cond then c1 else c2) \<in> derivable_caps s"
  using assms
  by auto

end

locale Write_Cap_Assm_Automaton =
  Write_Cap_Automaton CC ISA ex_traces invoked_caps invoked_indirect_caps
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
  and ex_traces :: bool and invoked_caps :: "'cap set" and invoked_indirect_caps :: "'cap set" +
  fixes ev_assms :: "'regval event \<Rightarrow> bool"
begin

sublocale Cap_Axiom_Assm_Automaton where enabled = enabled and use_mem_caps = "invoked_indirect_caps = {}"
proof
  fix s e
  assume "non_cap_event e"
  then show "enabled s e"
    by (cases e) auto
next
  fix s r v
  assume "r \<notin> special_reg_names"
  then show "enabled s (E_read_reg r v)"
    by auto
qed

lemma read_reg_trace_enabled:
  assumes t: "(read_reg r, t, m') \<in> Traces"
    and r: "name r \<in> privileged_regs ISA \<longrightarrow> system_reg_access s \<or> ex_traces"
  shows "trace_enabled s t"
  by (use t in \<open>auto simp: read_reg_def elim!: Read_reg_TracesE split: option.splits\<close>)
     (use r in \<open>auto\<close>)

lemma traces_enabled_read_reg:
  assumes "name r \<in> privileged_regs ISA \<longrightarrow> (system_reg_access s \<or> ex_traces)"
  shows "traces_enabled (read_reg r) s"
  using assms
  unfolding traces_enabled_def
  by (blast intro: read_reg_trace_enabled)

lemma write_reg_trace_enabled:
  assumes "(write_reg r v, t, m') \<in> Traces"
    and "enabled s (E_write_reg (name r) (regval_of r v))"
  shows "trace_enabled s t"
  using assms
  by (auto simp add: write_reg_def simp del: enabled.simps elim!: Write_reg_TracesE)

lemma traces_enabled_write_reg:
  assumes "enabled s (E_write_reg (name r) (regval_of r v))"
  shows "traces_enabled (write_reg r v) s"
  using assms
  unfolding traces_enabled_def
  by (blast intro: write_reg_trace_enabled)

lemma traces_enabled_read_mem[traces_enabledI]:
  shows "traces_enabled (read_mem BCa BCb rk addr_sz addr sz) s"
  unfolding read_mem_def read_mem_bytes_def maybe_fail_def
  by (auto split: option.splits simp: traces_enabled_def elim: Traces_cases)

lemma traces_enabled_read_memt[traces_enabledI]:
  shows "traces_enabled (read_memt BCa BCb rk addr sz) s"
  unfolding read_memt_def read_memt_bytes_def maybe_fail_def
  by (auto split: option.splits simp: traces_enabled_def elim: Traces_cases)

lemma traces_enabled_write_mem[traces_enabledI]:
  shows "traces_enabled (write_mem BCa BCb wk addr_sz addr sz data) s"
  unfolding write_mem_def maybe_fail_def
  by (auto split: option.splits simp: traces_enabled_def elim: Traces_cases)

lemma traces_enabled_write_memt[traces_enabledI]:
  assumes "\<forall>addr' bytes c r.
             nat_of_bv BCa addr = Some addr'
               \<and> mem_bytes_of_bits BCb data = Some bytes
               \<and> cap_of_mem_bytes_method CC bytes tag = Some c
               \<and> ev_assms (E_write_memt wk addr' (nat sz) bytes tag r)
             \<longrightarrow> c \<in> derivable_caps s"
  shows "traces_enabled (write_memt BCa BCb wk addr sz data tag) s"
  using assms
  unfolding write_memt_def maybe_fail_def derivable_caps_def
  by (fastforce split: option.splits simp: traces_enabled_def elim: Traces_cases)

lemma traces_enabled_reg_axioms:
  assumes "traces_enabled m initial" and "hasTrace t m"
    and "trace_assms t"
    and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps invoked_indirect_caps t"
    and "store_cap_mem_axiom CC ISA invoked_indirect_caps t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro recognises_store_cap_reg_read_reg_axioms;
      elim traces_enabled_accepts_fromI;
      auto)+

end

locale Write_Cap_Inv_Automaton =
  Write_Cap_Automaton CC ISA ex_traces invoked_caps invoked_indirect_caps +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and ex_traces :: bool and invoked_caps :: "'cap set" and invoked_indirect_caps :: "'cap set"
    and get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
    and invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set"
begin

sublocale Cap_Axiom_Inv_Automaton where enabled = enabled and use_mem_caps = "invoked_indirect_caps = {}"
proof
  fix s e
  assume "non_cap_event e"
  then show "enabled s e"
    by (cases e) auto
next
  fix s r v
  assume "r \<notin> special_reg_names"
  then show "enabled s (E_read_reg r v)"
    by auto
qed

lemma read_reg_trace_enabled:
  assumes t: "(read_reg r, t, m') \<in> Traces"
    and r: "name r \<in> privileged_regs ISA \<longrightarrow> system_reg_access s \<or> ex_traces"
  shows "trace_enabled s t"
  by (use t in \<open>auto simp: read_reg_def elim!: Read_reg_TracesE split: option.splits\<close>)
     (use r in \<open>auto\<close>)

lemma traces_enabled_read_reg:
  assumes "name r \<in> privileged_regs ISA \<longrightarrow> (system_reg_access s \<or> ex_traces)"
  shows "traces_enabled (read_reg r) s regs"
  using assms
  unfolding traces_enabled_def
  by (blast intro: read_reg_trace_enabled)

lemma write_reg_trace_enabled:
  assumes "(write_reg r v, t, m') \<in> Traces"
    and "enabled s (E_write_reg (name r) (regval_of r v))"
  shows "trace_enabled s t"
  using assms
  by (auto simp add: write_reg_def simp del: enabled.simps elim!: Write_reg_TracesE)

lemma traces_enabled_write_reg:
  assumes "enabled s (E_write_reg (name r) (regval_of r v))"
  shows "traces_enabled (write_reg r v) s regs"
  using assms
  unfolding traces_enabled_def
  by (blast intro: write_reg_trace_enabled)

lemma traces_enabled_reg_axioms:
  assumes "traces_enabled m initial regs" and "hasTrace t m"
    and "reads_regs_from inv_regs t regs" and "invariant regs"
    and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps invoked_indirect_caps t"
    and "store_cap_mem_axiom CC ISA invoked_indirect_caps t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro recognises_store_cap_reg_read_reg_axioms;
      elim traces_enabled_accepts_fromI[where regs = regs];
      auto)+

end

locale Capability_ISA_Fixed_Translation = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes translation_assms :: "'regval event \<Rightarrow> bool"
  assumes fixed_translation: "\<And>i t addr load. \<forall>e \<in> set t. translation_assms e \<Longrightarrow> translate_address ISA addr load (take i t) = translate_address ISA addr load []"
begin

abbreviation "translation_assms_trace t \<equiv> \<forall>e \<in> set t. translation_assms e"

end

fun non_store_event :: "'regval event \<Rightarrow> bool" where
  "non_store_event (E_write_mem _ paddr sz v _) = False"
| "non_store_event (E_write_memt _ paddr sz v tag _) = False"
| "non_store_event _ = True"

abbreviation non_store_trace :: "'regval trace \<Rightarrow> bool" where
  "non_store_trace t \<equiv> (\<forall>e \<in> set t. non_store_event e)"

lemma (in Cap_Axiom_Automaton) non_mem_trace_mem_axiomsI:
  assumes "non_mem_trace t"
  shows "store_mem_axiom CC ISA invoked_indirect_caps t" and "store_tag_axiom CC ISA t" and "load_mem_axiom CC ISA is_fetch invoked_indirect_caps t"
proof -
  have i: "non_mem_event (t ! i)" if "i < length t" for i
    using assms that
    by (auto simp: non_mem_trace_def)
  show "store_mem_axiom CC ISA invoked_indirect_caps t"
    using i
    by (fastforce simp: store_mem_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv elim!: writes_mem_val.elims)
  show "store_tag_axiom CC ISA t"
    using i
    by (fastforce simp: store_tag_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv elim!: writes_mem_val.elims)
  show "load_mem_axiom CC ISA is_fetch invoked_indirect_caps t"
    using i
    by (fastforce simp: load_mem_axiom_def reads_mem_val_at_idx_def bind_eq_Some_conv elim!: reads_mem_val.elims)
qed

locale Mem_Automaton = Capability_ISA_Fixed_Translation where CC = CC and ISA = ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes is_fetch :: bool
    and invoked_indirect_caps :: "'cap set"
begin

abbreviation invokes_indirect_caps where "invokes_indirect_caps \<equiv> (invoked_indirect_caps \<noteq> {})"

definition addrs_in_mem_region :: "'cap \<Rightarrow> acctype \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "addrs_in_mem_region c acctype vaddr paddr sz =
     (set (address_range vaddr sz) \<subseteq> get_mem_region CC c \<and>
      translate_address ISA vaddr acctype [] = Some paddr)"

definition has_access_permission :: "'cap \<Rightarrow> acctype \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "has_access_permission c acctype is_cap is_local_cap =
     (case acctype of
        Fetch \<Rightarrow> permits_execute_method CC c
      | Load \<Rightarrow> permits_load_method CC c \<and> (is_cap \<longrightarrow> permits_load_cap_method CC c)
      | Store \<Rightarrow> permits_store_method CC c \<and> (is_cap \<longrightarrow> permits_store_cap_method CC c) \<and>
                 (is_local_cap \<longrightarrow> permits_store_local_cap_method CC c))"

definition authorises_access :: "'cap \<Rightarrow> acctype \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "authorises_access c acctype is_cap is_local_cap vaddr paddr sz =
     (is_tagged_method CC c \<and>
      (is_sealed_method CC c \<longrightarrow> is_indirect_sentry_method CC c \<and> unseal_method CC c \<in> invoked_indirect_caps \<and> acctype = Load) \<and>
      addrs_in_mem_region c acctype vaddr paddr sz \<and>
      has_access_permission c acctype is_cap is_local_cap)"

definition legal_store :: "nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "legal_store sz v tag \<longleftrightarrow> (tag = B0 \<or> tag = B1) \<and> sz = length v"

definition access_enabled :: "('cap, 'regval) axiom_state \<Rightarrow> acctype \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "access_enabled s acctype vaddr paddr sz v tag =
     ((tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA) \<and>
      (acctype = Fetch \<longrightarrow> tag = B0) \<and>
      (acctype = PTW \<or>
       (\<exists>c' \<in> derivable (accessed_caps (invoked_indirect_caps = {}) s).
          let is_cap = tag \<noteq> B0 in
          let is_local_cap = mem_val_is_local_cap CC ISA v tag \<and> tag = B1 in
          authorises_access c' acctype is_cap is_local_cap vaddr paddr sz)))"

lemmas access_enabled_defs = access_enabled_def authorises_access_def addrs_in_mem_region_def
  has_access_permission_def legal_store_def

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_write_mem wk paddr sz v r) =
     (let acctype = if is_translation_event ISA (E_write_mem wk paddr sz v r) then PTW else Store in
      (\<exists>vaddr. access_enabled s acctype vaddr paddr sz v B0) \<and> legal_store sz v B0)"
| "enabled s (E_write_memt wk paddr sz v tag r) =
     (let acctype = if is_translation_event ISA (E_write_memt wk paddr sz v tag r) then PTW else Store in
      (\<exists>vaddr. access_enabled s acctype vaddr paddr sz v tag) \<and> legal_store sz v tag)"
| "enabled s (E_read_mem rk paddr sz v) =
     (let acctype =
        if is_translation_event ISA (E_read_mem rk paddr sz v) then PTW else
        if is_fetch then Fetch else
        Load
      in
      (\<exists>vaddr. access_enabled s acctype vaddr paddr sz v B0))"
| "enabled s (E_read_memt rk paddr sz v_tag) =
     (let acctype =
        if is_translation_event ISA (E_read_memt rk paddr sz v_tag) then PTW else
        if is_fetch then Fetch else
        Load
      in
      (\<exists>vaddr. access_enabled s acctype vaddr paddr sz (fst v_tag) (snd v_tag)))"
| "enabled s _ = True"

sublocale Cap_Axiom_Automaton where enabled = enabled and use_mem_caps = "invoked_indirect_caps = {}" ..

lemma accepts_store_mem_axiom:
  assumes *: "translation_assms_trace t" and  **: "accepts t"
  shows "store_mem_axiom CC ISA invoked_indirect_caps t"
  using accepts_from_nth_enabledI[OF **]
  unfolding store_mem_axiom_def
  unfolding writes_mem_val_at_idx_def cap_derivable_iff_derivable
  unfolding translation_event_at_idx_def
  unfolding fixed_translation[OF *]
  by (fastforce simp: access_enabled_defs bind_eq_Some_conv elim!: writes_mem_val.elims)

lemma accepts_store_tag_axiom:
  assumes "accepts t"
  shows "store_tag_axiom CC ISA t"
  using accepts_from_nth_enabledI[OF assms]
  unfolding store_tag_axiom_def writes_mem_val_at_idx_def
  by (fastforce simp: access_enabled_defs bind_eq_Some_conv Let_def elim!: writes_mem_val.elims)

lemma accepts_load_mem_axiom:
  assumes *: "translation_assms_trace t" and  **: "accepts t"
  shows "load_mem_axiom CC ISA is_fetch invoked_indirect_caps t"
  unfolding load_mem_axiom_def
  unfolding reads_mem_val_at_idx_def cap_derivable_iff_derivable
  unfolding translation_event_at_idx_def
  unfolding fixed_translation[OF *]
  by (auto split: option.splits elim!: reads_mem_val.elims dest!: accepts_from_nth_enabledI[OF **] split del: if_split;
      cases is_fetch; fastforce simp: access_enabled_defs)

lemma non_mem_event_enabledI:
  "enabled s e" if "non_mem_event e"
  using that
  by (auto elim: non_mem_event.elims)

lemma non_mem_trace_enabledI:
  "trace_enabled s t" if "non_mem_trace t"
  using that
  by (induction t arbitrary: s) (auto intro: non_mem_event_enabledI)

end

locale Mem_Assm_Automaton =
  Mem_Automaton translation_assms CC ISA is_fetch invoked_indirect_caps
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and translation_assms :: "'regval event \<Rightarrow> bool"
    and is_fetch :: bool and ex_traces :: bool
    and invoked_indirect_caps :: "'cap set" +
  fixes extra_assms :: "'regval event \<Rightarrow> bool"
begin

definition "ev_assms e \<equiv> translation_assms e \<and> extra_assms e"

sublocale Cap_Axiom_Assm_Automaton
  where enabled = enabled and ex_traces = ex_traces and ev_assms = ev_assms and use_mem_caps = "invoked_indirect_caps = {}"
proof
  fix s e
  assume "non_cap_event e"
  then show "enabled s e"
    by (cases e) auto
next
  fix s r v
  assume "r \<notin> special_reg_names"
  then show "enabled s (E_read_reg r v)"
    by auto
qed

lemma non_mem_exp_trace_enabledI:
  "trace_enabled s t" if "non_mem_exp m" and "(m, t, m') \<in> Traces"
  using that
  by (auto simp: non_mem_exp_def intro: non_mem_trace_enabledI)

lemma non_mem_exp_traces_enabledI:
  "traces_enabled m s" if "non_mem_exp m"
  using that
  by (auto simp: traces_enabled_def intro: non_mem_exp_trace_enabledI)

lemma traces_enabled_mem_axioms:
  assumes "traces_enabled m initial" and "hasTrace t m"
    and "trace_assms t"
    and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
  shows "store_mem_axiom CC ISA invoked_indirect_caps t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA is_fetch invoked_indirect_caps t"
  using assms
  by (intro accepts_store_mem_axiom accepts_store_tag_axiom accepts_load_mem_axiom
            traces_enabled_accepts_fromI;
      auto simp: trace_assms_def ev_assms_def)+

lemma traces_enabled_Read_mem:
  assumes "\<And>v. traces_enabled (m v) (axiom_step s (E_read_mem rk paddr sz v))"
    and "\<And>v. enabled s (E_read_mem rk paddr sz v)"
  shows "traces_enabled (Read_mem rk paddr sz m) s"
  using assms
  by (fastforce simp: traces_enabled_def elim!: Traces_cases[where m = "Read_mem rk paddr sz m"])

lemma traces_enabled_read_mem:
  assumes "\<And>paddr v. nat_of_bv BC_addr addr = Some paddr \<Longrightarrow> enabled s (E_read_mem rk paddr (nat sz) v)"
  shows "traces_enabled (read_mem BC_addr BC_val rk addr_sz addr sz) s"
  using assms
  by (auto intro!: traces_enabled_Read_mem traces_enabled_bind
                   non_cap_expI[THEN non_cap_exp_traces_enabledI]
      simp: read_mem_def read_mem_bytes_def maybe_fail_def split: option.splits)

lemma traces_enabled_Read_memt:
  assumes "\<And>v tag. traces_enabled (m (v, tag)) (axiom_step s (E_read_memt rk paddr sz (v, tag)))"
    and "\<And>v tag. enabled s (E_read_memt rk paddr sz (v, tag))"
  shows "traces_enabled (Read_memt rk paddr sz m) s"
  using assms
  by (fastforce simp: traces_enabled_def elim!: Traces_cases[where m = "Read_memt rk paddr sz m"])

lemma traces_enabled_read_memt:
  assumes "\<And>paddr v tag. nat_of_bv BC_addr addr = Some paddr \<Longrightarrow> enabled s (E_read_memt rk paddr (nat sz) (v, tag))"
  shows "traces_enabled (read_memt BC_addr BC_val rk addr sz) s"
  using assms
  by (auto intro!: traces_enabled_Read_memt traces_enabled_bind
                   non_cap_expI[THEN non_cap_exp_traces_enabledI]
      simp: read_memt_def read_memt_bytes_def maybe_fail_def split: option.splits)

end

locale Mem_Inv_Automaton =
  Mem_Automaton translation_assms CC ISA is_fetch invoked_indirect_caps +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and translation_assms :: "'regval event \<Rightarrow> bool"
    and is_fetch :: bool and ex_traces :: bool
    and invoked_indirect_caps :: "'cap set"
    and get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
    and invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set"
begin

sublocale Cap_Axiom_Inv_Automaton where enabled = enabled and ex_traces = ex_traces and use_mem_caps = "invoked_indirect_caps = {}"
proof
  fix s e
  assume "non_cap_event e"
  then show "enabled s e"
    by (cases e) auto
next
  fix s r v
  assume "r \<notin> special_reg_names"
  then show "enabled s (E_read_reg r v)"
    by auto
qed

lemma non_mem_exp_trace_enabledI:
  "trace_enabled s t" if "non_mem_exp m" and "(m, t, m') \<in> Traces"
  using that
  by (auto simp: non_mem_exp_def intro: non_mem_trace_enabledI)

lemma non_mem_exp_traces_enabledI:
  "traces_enabled m s regs" if "non_mem_exp m"
  using that
  by (auto simp: traces_enabled_def intro: non_mem_exp_trace_enabledI)

lemma traces_enabled_mem_axioms:
  assumes "traces_enabled m initial regs" and "hasTrace t m"
    and "reads_regs_from inv_regs t regs" and "invariant regs"
    and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
    and "translation_assms_trace t"
  shows "store_mem_axiom CC ISA invoked_indirect_caps t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA is_fetch invoked_indirect_caps t"
  using assms
  by (intro accepts_store_mem_axiom accepts_store_tag_axiom accepts_load_mem_axiom
            traces_enabled_accepts_fromI[where m = m and regs = regs];
      auto)+

end

(*locale Store_Mem_Automaton = Capability_ISA_Fixed_Translation CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
begin

fun store_enabled :: "('cap, 'regval) axiom_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "store_enabled s paddr sz v tag =
     (length v = sz \<and>
      (tag = B0 \<or> tag = B1) \<and>
      (tag = B1 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA) \<and>
      (paddr \<in> translation_tables ISA [] \<or>
       (\<exists>c' vaddr. c' \<in> derivable (accessed_caps s) \<and>
          is_tagged_method CC c' \<and>
          \<not> is_sealed_method CC c' \<and>
          translate_address ISA vaddr Store [] = Some paddr \<and>
          set (address_range vaddr sz) \<subseteq> get_mem_region_method CC c' \<and>
          (if mem_val_is_cap CC ISA v tag \<and> tag = B1
           then permit_store_capability (get_perms_method CC c')
           else permit_store (get_perms_method CC c')) \<and>
          (mem_val_is_local_cap CC ISA v tag \<and> tag = B1 \<longrightarrow>
           permit_store_local_capability (get_perms_method CC c')))))"

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_write_mem _ paddr sz v _) = store_enabled s paddr sz v B0"
| "enabled s (E_write_memt _ paddr sz v tag _) = store_enabled s paddr sz v tag"
| "enabled s _ = True"

sublocale Cap_Axiom_Automaton CC ISA enabled ..

lemma non_store_event_enabledI:
  assumes "non_store_event e"
  shows "enabled s e"
  using assms
  by (cases e) auto

lemma non_store_trace_enabledI:
  assumes "non_store_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t arbitrary: s) (auto intro: non_store_event_enabledI)

lemma non_cap_event_enabledI:
  assumes "non_cap_event e"
  shows "enabled s e"
  using assms
  by (elim non_cap_event.elims) auto

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabledI non_cap_event_axiom_step_inv)

lemma non_cap_exp_trace_enabledI:
  assumes "non_cap_exp m"
    and "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF assms])
     (auto intro: non_cap_trace_enabledI simp: trace_enabled_append_iff)

lemma accepts_iff_store_mem_tag_axioms:
  assumes "translation_assms t"
  shows "accepts t \<longleftrightarrow> store_mem_axiom CC ISA t \<and> store_tag_axiom CC ISA t"
proof
  assume *: "accepts t"
  show "store_mem_axiom CC ISA t \<and> store_tag_axiom CC ISA t"
  proof (unfold store_mem_axiom_def store_tag_axiom_def, fold all_conj_distrib, intro allI, goal_cases Idx)
    case (Idx i paddr sz v tag)
    then show ?case
      using accepts_from_nth_enabledI[OF *]
      unfolding writes_mem_val_at_idx_def cap_derivable_iff_derivable
      unfolding fixed_translation_tables[OF assms] fixed_translation[OF assms]
      by (fastforce simp: bind_eq_Some_conv elim!: writes_mem_val.elims)
  qed
next
  assume *: "store_mem_axiom CC ISA t \<and> store_tag_axiom CC ISA t"
  show "accepts t"
  proof (unfold accepts_from_iff_all_enabled_final, intro conjI allI impI TrueI)
    fix i
    assume "i < length t"
    then show "enabled (run initial (take i t)) (t ! i)"
      using *[unfolded store_mem_axiom_def store_tag_axiom_def, folded all_conj_distrib, rule_format, of i]
      unfolding writes_mem_val_at_idx_def cap_derivable_iff_derivable
      unfolding fixed_translation_tables[OF assms] fixed_translation[OF assms]
      by (cases "t ! i") (auto cong: conj_cong disj_cong)
  qed
qed

lemma recognises_store_mem_tag_axioms:
  assumes "translation_assms t" and "accepts t"
  shows "store_mem_axiom CC ISA t" and "store_tag_axiom CC ISA t"
  using assms(2)
  unfolding accepts_iff_store_mem_tag_axioms[OF assms(1)]
  by auto

end

fun non_load_event :: "'regval event \<Rightarrow> bool" where
  "non_load_event (E_read_mem _ paddr sz v) = False"
| "non_load_event (E_read_memt _ paddr sz v_tag) = False"
| "non_load_event _ = True"

abbreviation non_load_trace :: "'regval trace \<Rightarrow> bool" where
  "non_load_trace t \<equiv> (\<forall>e \<in> set t. non_load_event e)"

lemma non_load_trace_load_mem_axiomI:
  assumes "non_load_trace t"
  shows "load_mem_axiom CC ISA is_fetch t"
proof -
  have i: "non_load_event (t ! i)" if "i < length t" for i
    using assms that
    by auto
  show "load_mem_axiom CC ISA is_fetch t"
    using i
    by (fastforce simp: load_mem_axiom_def reads_mem_val_at_idx_def bind_eq_Some_conv elim!: reads_mem_val.elims)
qed

locale Load_Mem_Automaton = Capability_ISA_Fixed_Translation CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes is_fetch :: bool
begin

fun load_enabled :: "('cap, 'regval) axiom_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "load_enabled s paddr sz v tag =
    (paddr \<in> translation_tables ISA [] \<or>
    (\<exists>c' vaddr.
        c' \<in> derivable (accessed_caps s) \<and>
        is_tagged_method CC c' \<and>
        \<not> is_sealed_method CC c' \<and>
        translate_address ISA vaddr (if is_fetch then Load else Fetch) [] = Some paddr \<and>
        set (address_range vaddr sz) \<subseteq> get_mem_region_method CC c' \<and>
        (if is_fetch \<and> tag = B0
         then permit_execute (get_perms_method CC c')
         else permit_load (get_perms_method CC c')) \<and>
        (tag \<noteq> B0 \<longrightarrow> permit_load_capability (get_perms_method CC c') \<and> sz = tag_granule ISA \<and>
                      address_tag_aligned ISA paddr)))"

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_read_mem _ paddr sz v) = load_enabled s paddr sz v B0"
| "enabled s (E_read_memt _ paddr sz v_tag) = load_enabled s paddr sz (fst v_tag) (snd v_tag)"
| "enabled s _ = True"

sublocale Cap_Axiom_Automaton CC ISA enabled ..

lemma non_load_event_enabledI:
  assumes "non_load_event e"
  shows "enabled s e"
  using assms
  by (cases e) auto

lemma non_load_trace_enabledI:
  assumes "non_load_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t arbitrary: s) (auto intro: non_load_event_enabledI)

lemma non_cap_event_enabledI:
  assumes "non_cap_event e"
  shows "enabled s e"
  using assms
  by (elim non_cap_event.elims) auto

lemma non_cap_trace_enabledI:
  assumes "non_cap_trace t"
  shows "trace_enabled s t"
  using assms
  by (induction t) (auto simp: non_cap_event_enabledI non_cap_event_axiom_step_inv)

lemma non_cap_exp_trace_enabledI:
  assumes "non_cap_exp m"
    and "(m, t, m') \<in> Traces"
  shows "trace_enabled s t"
  by (cases rule: non_cap_exp_Traces_cases[OF assms])
     (auto intro: non_cap_trace_enabledI simp: trace_enabled_append_iff)

lemma recognises_load_mem_axiom:
  assumes "translation_assms t"
  shows "accepts t \<longleftrightarrow> load_mem_axiom CC ISA is_fetch t"
proof
  assume *: "accepts t"
  show "load_mem_axiom CC ISA is_fetch t"
  proof (unfold load_mem_axiom_def, intro allI impI, elim conjE, goal_cases Idx)
    case (Idx i paddr sz v tag)
    then show ?case
      using accepts_from_nth_enabledI[OF *]
      unfolding cap_derivable_iff_derivable reads_mem_val_at_idx_def
      unfolding fixed_translation_tables[OF assms] fixed_translation[OF assms]
      by (cases "t ! i"; fastforce simp add: bind_eq_Some_conv)
  qed
next
  assume *: "load_mem_axiom CC ISA is_fetch t"
  show "accepts t"
  proof (unfold accepts_from_iff_all_enabled_final, intro conjI allI impI TrueI)
    fix i
    assume "i < length t"
    then show "enabled (run initial (take i t)) (t ! i)"
      using *[unfolded load_mem_axiom_def, rule_format, of i]
      unfolding reads_mem_val_at_idx_def cap_derivable_iff_derivable
      unfolding fixed_translation_tables[OF assms] fixed_translation[OF assms]
      by (cases "t ! i"; fastforce)
  qed
qed

end*)

end
