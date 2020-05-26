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
  accessed_caps :: "'cap set"
  system_reg_access :: bool
  read_from_KCC :: "'regval set"
  written_regs :: "string set"

locale Cap_Axiom_Automaton = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool"
begin

definition accessible_regs :: "('cap, 'regval) axiom_state \<Rightarrow> register_name set" where
  "accessible_regs s = {r. (r \<in> PCC ISA \<union> IDC ISA \<longrightarrow> r \<notin> written_regs s) \<and> (r \<in> privileged_regs ISA \<longrightarrow> system_reg_access s)}"

definition axiom_step :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> ('cap, 'regval) axiom_state" where
  "axiom_step s e = \<lparr>accessed_caps = accessed_caps s \<union> accessed_mem_caps e \<union> accessed_reg_caps (accessible_regs s) e,
                     system_reg_access = system_reg_access s \<or> allows_system_reg_access (accessible_regs s) e,
                     read_from_KCC = read_from_KCC s \<union> {v. \<exists>r \<in> KCC ISA. e = E_read_reg r v},
                     written_regs = written_regs s \<union> {r. \<exists>v c. e = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}\<rparr>"

lemma step_selectors[simp]:
  "accessed_caps (axiom_step s e) = accessed_caps s \<union> accessed_mem_caps e \<union> accessed_reg_caps (accessible_regs s) e"
  "system_reg_access (axiom_step s e) \<longleftrightarrow> system_reg_access s \<or> allows_system_reg_access (accessible_regs s) e"
  "read_from_KCC (axiom_step s e) = read_from_KCC s \<union> {v. \<exists>r \<in> KCC ISA. e = E_read_reg r v}"
  "written_regs (axiom_step s e) = written_regs s \<union> {r. \<exists>v c. e = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c}"
  by (auto simp: axiom_step_def)

abbreviation "initial \<equiv> \<lparr>accessed_caps = {}, system_reg_access = False, read_from_KCC = {}, written_regs = {}\<rparr>"

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

lemma accessed_caps_run_take_eq[simp]:
  "available_caps CC ISA i t = accessed_caps (run initial (take i t))"
proof (induction i)
  case (Suc i)
  then show ?case
    by (cases "i < length t") (auto simp add: available_caps_Suc take_Suc_conv_app_nth)
qed auto

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

lemma non_cap_exp_bool_of_bitU_fail[non_cap_expI]:
  "non_cap_exp (bool_of_bitU_fail b)"
  unfolding bool_of_bitU_fail_def
  by (cases b) (auto intro: non_cap_expI)

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

method non_cap_expI uses simp intro =
  (auto simp: simp intro!: non_cap_expI non_cap_exp_if non_cap_exp_read_non_cap_reg non_cap_exp_write_non_cap_reg
        split del: if_split split: option.split sum.split prod.split)

lemmas non_mem_exp_combinators =
  non_mem_exp_bindI non_mem_exp_if non_mem_exp_let non_mem_exp_and_boolM non_mem_exp_or_boolM
  non_mem_exp_foreachM non_mem_exp_try_catch non_mem_exp_catch_early_return non_mem_exp_liftR

method non_mem_expI uses simp intro =
  (auto simp: simp intro!: intro non_mem_expI non_mem_exp_combinators non_cap_expI[THEN non_cap_exp_non_mem_exp]
        split del: if_split split: option.split sum.split prod.split)

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
  fixes ex_traces :: bool and invoked_caps :: "'cap set"
begin

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_write_reg r v) =
     (\<forall>c. (c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c)
         \<longrightarrow>
         (c \<in> derivable (accessed_caps s) \<or>
          (c \<in> exception_targets ISA (read_from_KCC s) \<and> ex_traces \<and> r \<in> PCC ISA) \<or>
          (\<exists>cs. c \<in> invoked_caps \<and> cs \<in> derivable (accessed_caps s) \<and>
                is_sentry_method CC cs \<and> is_sealed_method CC cs \<and>
                leq_cap CC c (unseal_method CC cs) \<and> r \<in> PCC ISA) \<or>
          (\<exists>cc cd. c \<in> invoked_caps \<and> invokable CC cc cd \<and>
                   cc \<in> derivable (accessed_caps s) \<and> cd \<in> derivable (accessed_caps s) \<and>
                   (r \<in> PCC ISA \<and> leq_cap CC c (unseal_method CC cc) \<or>
                    r \<in> IDC ISA \<and> leq_cap CC c (unseal_method CC cd)))))"
| "enabled s (E_read_reg r v) = (r \<in> privileged_regs ISA \<longrightarrow> (system_reg_access s \<or> ex_traces))"
| "enabled s (E_write_memt _ addr sz bytes tag _) =
     (\<forall>c.  cap_of_mem_bytes_method CC bytes tag = Some c \<and> is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_caps s))"
| "enabled s _ = True"

lemma enabled_E_write_reg_cases:
  assumes "enabled s (E_write_reg r v)"
    and "c \<in> caps_of_regval ISA v"
    and "is_tagged_method CC c"
  obtains (Derivable) "c \<in> derivable (accessed_caps s)"
  | (KCC) "c \<in> exception_targets ISA (read_from_KCC s)" and "ex_traces" and
      "r \<in> PCC ISA" and "c \<notin> derivable (accessed_caps s)"
  | (Sentry) cs where "c \<in> invoked_caps" and "cs \<in> derivable (accessed_caps s)" and
      "is_sentry_method CC cs" and "is_sealed_method CC cs" and
      "leq_cap CC c (unseal_method CC cs)" and "r \<in> PCC ISA"
  | (CCall) cc cd where "c \<in> invoked_caps" and "invokable CC cc cd" and
      "cc \<in> derivable (accessed_caps s)" and "cd \<in> derivable (accessed_caps s)" and
      "r \<in> PCC ISA \<and> leq_cap CC c (unseal_method CC cc) \<or> r \<in> IDC ISA \<and> leq_cap CC c (unseal_method CC cd)" and
      "c \<notin> derivable (accessed_caps s)"
  using assms by (cases "c \<in> derivable (accessed_caps s)") auto

sublocale Cap_Axiom_Automaton CC ISA enabled ..

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
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps t"
    and "store_cap_mem_axiom CC ISA t"
    and "read_reg_axiom CC ISA ex_traces t"
proof -
  show "read_reg_axiom CC ISA ex_traces t"
    using assms (*read_from_KCC_run_take_eq[of "length t" t]*)
    unfolding accepts_from_iff_all_enabled_final read_reg_axiom_def
    by (auto elim!: enabled.elims)
  show "store_cap_reg_axiom CC ISA ex_traces invoked_caps t"
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
        case (CCall cc cd)
        then show ?thesis
          by (auto simp: cap_derivable_iff_derivable)
      qed
    qed auto
  qed
  show "store_cap_mem_axiom CC ISA t"
    using assms
    unfolding accepts_from_iff_all_enabled_final store_cap_mem_axiom_def
    by (auto simp: cap_derivable_iff_derivable writes_mem_cap_Some_iff)
qed

end

locale Cap_Axiom_Assm_Automaton = Cap_Axiom_Automaton CC ISA enabled
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" +
  fixes ex_traces :: bool
    and ev_assms :: "'regval event \<Rightarrow> bool"
  assumes non_cap_event_enabled: "\<And>e. non_cap_event e \<Longrightarrow> enabled s e"
    and read_non_special_regs_enabled: "\<And>r v. r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<Longrightarrow> enabled s (E_read_reg r v)"
begin

definition "trace_assms t \<equiv> \<forall>e \<in> set t. ev_assms e"

lemma trace_assms_append[iff]: "trace_assms (t1 @ t2) \<longleftrightarrow> trace_assms t1 \<and> trace_assms t2"
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

lemma traces_enabled_foreachM_inv:
  assumes "\<And>x vars s. P vars s \<Longrightarrow> x \<in> set xs \<Longrightarrow> traces_enabled (body x vars) s"
    and "\<And>x vars s t vars'. P vars s \<Longrightarrow> x \<in> set xs \<Longrightarrow> Run (body x vars) t vars' \<Longrightarrow> P vars' (run s t)"
    and "P vars s"
  shows "traces_enabled (foreachM xs vars body) s"
  by (use assms in \<open>induction xs arbitrary: vars s\<close>;
      fastforce intro!: traces_enabledI intro: non_cap_exp_traces_enabledI non_cap_expI)

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

lemma accessible_regs_no_writes_run:
  assumes t: "Run m t a"
    and m: "runs_no_reg_writes_to {r} m"
    and s: "r \<in> accessible_regs s"
  shows "r \<in> accessible_regs (run s t)"
proof -
  have no_write: "\<forall>v. E_write_reg r v \<notin> set t"
    using m t
    by (auto simp: runs_no_reg_writes_to_def)
  show ?thesis
  proof (use s no_write in \<open>induction t arbitrary: s\<close>)
    case (Cons e t)
    then have "r \<in> accessible_regs (axiom_step s e)" and "\<forall>v. E_write_reg r v \<notin> set t"
      by (auto simp: accessible_regs_def)
    from Cons.IH[OF this] show ?case by auto
  qed auto
qed

lemma no_reg_writes_to_mono:
  assumes "runs_no_reg_writes_to Rs m"
    and "Rs' \<subseteq> Rs"
  shows "runs_no_reg_writes_to Rs' m"
  using assms
  by (auto simp: runs_no_reg_writes_to_def)

lemma accessible_regs_no_writes_run_subset:
  assumes t: "Run m t a" and m: "runs_no_reg_writes_to Rs m"
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

method accessible_regs_step uses simp assms =
  ((erule accessible_regsE eqTrueE)
    | (rule accessible_regsI TrueI)
    | (erule accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>))

method accessible_regsI_with methods solve uses simp assms =
  ((erule accessible_regsE eqTrueE; accessible_regsI_with solve simp: simp assms: assms)
    | (rule accessible_regsI TrueI; accessible_regsI_with solve simp: simp assms: assms)
    | (erule accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>,
       accessible_regsI_with solve simp: simp assms: assms)
    | solve)

method accessible_regsI uses simp assms =
  (accessible_regsI_with
     \<open>(use assms in \<open>no_reg_writes_toI simp: simp\<close>)
       | (use assms in \<open>auto simp: simp\<close>)\<close>
     simp: simp assms: assms)

definition "derivable_caps s \<equiv> {c. is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_caps s)}"

named_theorems derivable_capsI
named_theorems derivable_capsE

lemma accessed_caps_run_mono:
  "accessed_caps s \<subseteq> accessed_caps (run s t)"
  by (rule subsetI) (induction t arbitrary: s; auto)

lemma derivable_caps_run_mono:
  "derivable_caps s \<subseteq> derivable_caps (run s t)"
  using derivable_mono[OF accessed_caps_run_mono]
  by (auto simp: derivable_caps_def)

lemma derivable_caps_run_imp:
  "c \<in> derivable_caps s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  using derivable_caps_run_mono
  by auto

method derivable_caps_step =
  (rule derivable_capsI TrueI
      | erule derivable_capsE eqTrueE
      | rule derivable_caps_run_imp)

method derivable_capsI_with methods solve uses intro elim simp assms =
  ((rule intro derivable_capsI TrueI
      | erule elim derivable_capsE eqTrueE
      | rule derivable_caps_run_imp
      | solve (*
      | solves \<open>use assms in \<open>auto simp: simp\<close>\<close>*));
   derivable_capsI_with solve intro: intro elim: elim simp: simp assms: assms)

method derivable_capsI uses intro elim simp assms =
  (derivable_capsI_with
     \<open>(solves \<open>accessible_regsI simp: simp assms: assms\<close>)\<close>
     intro: intro elim: elim simp: simp assms: assms)

method try_simp_traces_enabled =
  ((match conclusion in \<open>traces_enabled m2 (run s t)\<close> for m2 s t \<Rightarrow>
     \<open>match premises in m1: \<open>Run m1 t a\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_traces_enabled_runE[OF m1], solves \<open>non_cap_expI\<close>)?\<close>\<close>
   \<bar> \<open>early_returns_enabled m2 (run s t)\<close> for m2 s t \<Rightarrow>
     \<open>match premises in m1: \<open>Run m1 t a\<close> for m1 a \<Rightarrow>
        \<open>(rule non_cap_exp_Run_inv_early_returns_enabled_runE[OF m1], solves \<open>non_cap_expI\<close>)?\<close>\<close>)?)

named_theorems traces_enabled_combinatorI

lemmas traces_enabled_builtin_combinatorsI =
  traces_enabled_bind traces_enabled_and_boolM traces_enabled_or_boolM
  early_returns_enabled_bind early_returns_enabled_and_boolM early_returns_enabled_or_boolM

named_theorems traces_enabled_split
declare option.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare prod.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare sum.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]
declare bool.split[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

method traces_enabled_step uses intro elim =
  ((rule intro TrueI)
    | (erule elim eqTrueE)
    | ((rule traces_enabled_combinatorI traces_enabled_builtin_combinatorsI[rotated], try_simp_traces_enabled))
    | (rule traces_enabled_split[THEN iffD2]; intro allI conjI impI))

method traces_enabledI_with methods solve uses intro elim =
  ((rule intro TrueI; traces_enabledI_with solve intro: intro elim: elim)
    | (erule elim eqTrueE; traces_enabledI_with solve intro: intro elim: elim)
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
  ((traces_enabled_step intro: intro elim: elim; traces_enabledI simp: simp intro: intro elim: elim assms: assms)
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

locale Cap_Axiom_Inv_Automaton = Cap_Axiom_Automaton CC ISA enabled +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool"
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

lemma accessible_regs_no_writes_run:
  assumes t: "Run m t a"
    and m: "runs_no_reg_writes_to {r} m"
    and s: "r \<in> accessible_regs s"
  shows "r \<in> accessible_regs (run s t)"
proof -
  have no_write: "\<forall>v. E_write_reg r v \<notin> set t"
    using m t
    by (auto simp: runs_no_reg_writes_to_def Run_inv_def)
  show ?thesis
  proof (use s no_write in \<open>induction t arbitrary: s\<close>)
    case (Cons e t)
    then have "r \<in> accessible_regs (axiom_step s e)" and "\<forall>v. E_write_reg r v \<notin> set t"
      by (auto simp: accessible_regs_def)
    from Cons.IH[OF this] show ?case by auto
  qed auto
qed

lemma no_reg_writes_to_mono:
  assumes "runs_no_reg_writes_to Rs m"
    and "Rs' \<subseteq> Rs"
  shows "runs_no_reg_writes_to Rs' m"
  using assms
  by (auto simp: runs_no_reg_writes_to_def)

lemma accessible_regs_no_writes_run_subset:
  assumes t: "Run m t a" and m: "runs_no_reg_writes_to Rs m"
    and Rs: "Rs \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using t Rs no_reg_writes_to_mono[OF m]
  by (auto intro: accessible_regs_no_writes_run)

lemma accessible_regs_no_writes_run_inv_subset:
  assumes t: "Run_inv m t a regs" and m: "runs_no_reg_writes_to Rs m"
    and Rs: "Rs \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using assms
  by (intro accessible_regs_no_writes_run_subset) (auto simp: Run_inv_def)

(*method accessible_regsI uses simp assms =
  (match conclusion in \<open>Rs \<subseteq> accessible_regs (run s t)\<close> for Rs s t \<Rightarrow>
     \<open>match premises in t: \<open>Run_inv m t a regs\<close> for m a regs \<Rightarrow>
        \<open>rule accessible_regs_no_writes_run_subset[OF t],
         solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>,
         accessible_regsI simp: simp assms: assms\<close>\<close>\<close>
   \<bar> \<open>Rs \<subseteq> accessible_regs s\<close> for Rs s \<Rightarrow> \<open>use assms in \<open>auto simp: simp\<close>\<close>)*)

named_theorems accessible_regsE
named_theorems accessible_regsI

method accessible_regs_step uses simp assms =
  ((erule accessible_regsE eqTrueE)
    | (rule accessible_regsI preserves_invariantI TrueI)
    | (erule accessible_regs_no_writes_run_inv_subset accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>))

method accessible_regsI_with methods solve uses simp assms =
  ((erule accessible_regsE eqTrueE; accessible_regsI_with solve simp: simp assms: assms)
    | (rule accessible_regsI preserves_invariantI TrueI; accessible_regsI_with solve simp: simp assms: assms)
    | (erule accessible_regs_no_writes_run_inv_subset accessible_regs_no_writes_run_subset,
       solves \<open>use assms in \<open>no_reg_writes_toI simp: simp\<close>\<close>,
       accessible_regsI_with solve simp: simp assms: assms)
    | solve)

method accessible_regsI uses simp assms =
  (accessible_regsI_with
     \<open>(use assms in \<open>no_reg_writes_toI simp: simp\<close>)
       | (use assms in \<open>preserves_invariantI simp: simp\<close>)
       | (use assms in \<open>auto simp: simp\<close>)\<close>
     simp: simp assms: assms)

definition "derivable_caps s \<equiv> {c. is_tagged_method CC c \<longrightarrow> c \<in> derivable (accessed_caps s)}"

named_theorems derivable_capsI
named_theorems derivable_capsE

lemma accessed_caps_run_mono:
  "accessed_caps s \<subseteq> accessed_caps (run s t)"
  by (rule subsetI) (induction t arbitrary: s; auto)

lemma derivable_caps_run_mono:
  "derivable_caps s \<subseteq> derivable_caps (run s t)"
  using derivable_mono[OF accessed_caps_run_mono]
  by (auto simp: derivable_caps_def)

lemma derivable_caps_run_imp:
  "c \<in> derivable_caps s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  using derivable_caps_run_mono
  by auto

method derivable_caps_step =
  (rule derivable_capsI preserves_invariantI TrueI
      | erule derivable_capsE eqTrueE
      | rule derivable_caps_run_imp)

method derivable_capsI_with methods solve uses intro elim simp assms =
  ((rule intro derivable_capsI preserves_invariantI TrueI
      | erule elim derivable_capsE eqTrueE
      | rule derivable_caps_run_imp
      | solve (*
      | solves \<open>use assms in \<open>auto simp: simp\<close>\<close>*));
   derivable_capsI_with solve intro: intro elim: elim simp: simp assms: assms)

method derivable_capsI uses intro elim simp assms =
  (derivable_capsI_with
     \<open>(solves \<open>accessible_regsI simp: simp assms: assms\<close>)
       | (solves \<open>preserves_invariantI intro: intro simp: simp elim: elim\<close>)\<close>
     intro: intro elim: elim simp: simp assms: assms)

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
  ((traces_enabled_step intro: intro elim: elim; traces_enabledI simp: simp intro: intro elim: elim assms: assms)
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
  Write_Cap_Automaton CC ISA ex_traces invoked_caps
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
  and ex_traces :: bool and invoked_caps :: "'cap set" +
  fixes ev_assms :: "'regval event \<Rightarrow> bool"
begin

sublocale Cap_Axiom_Assm_Automaton where enabled = enabled
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

lemma traces_enabled_reg_axioms:
  assumes "traces_enabled m initial" and "hasTrace t m"
    and "trace_assms t"
    and "hasException t m \<or> hasFailure t m \<longrightarrow> ex_traces"
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps t"
    and "store_cap_mem_axiom CC ISA t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro recognises_store_cap_reg_read_reg_axioms;
      elim traces_enabled_accepts_fromI;
      auto)+

end

locale Write_Cap_Inv_Automaton =
  Write_Cap_Automaton CC ISA ex_traces invoked_caps +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and ex_traces :: bool and invoked_caps :: "'cap set"
    and get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
    and invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set"
begin

sublocale Cap_Axiom_Inv_Automaton where enabled = enabled
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
  shows "store_cap_reg_axiom CC ISA ex_traces invoked_caps t"
    and "store_cap_mem_axiom CC ISA t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro recognises_store_cap_reg_read_reg_axioms;
      elim traces_enabled_accepts_fromI[where regs = regs];
      auto)+

end

locale Capability_ISA_Fixed_Translation = Capability_ISA CC ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes translation_assms :: "'regval trace \<Rightarrow> bool"
  assumes fixed_translation: "\<And>i t addr load. translation_assms t \<Longrightarrow> translate_address ISA addr load (take i t) = translate_address ISA addr load []"

fun non_store_event :: "'regval event \<Rightarrow> bool" where
  "non_store_event (E_write_mem _ paddr sz v _) = False"
| "non_store_event (E_write_memt _ paddr sz v tag _) = False"
| "non_store_event _ = True"

abbreviation non_store_trace :: "'regval trace \<Rightarrow> bool" where
  "non_store_trace t \<equiv> (\<forall>e \<in> set t. non_store_event e)"

lemma (in Cap_Axiom_Automaton) non_mem_trace_mem_axiomsI:
  assumes "non_mem_trace t"
  shows "store_mem_axiom CC ISA t" and "store_tag_axiom CC ISA t" and "load_mem_axiom CC ISA is_fetch t"
proof -
  have i: "non_mem_event (t ! i)" if "i < length t" for i
    using assms that
    by (auto simp: non_mem_trace_def)
  show "store_mem_axiom CC ISA t"
    using i
    by (fastforce simp: store_mem_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv elim!: writes_mem_val.elims)
  show "store_tag_axiom CC ISA t"
    using i
    by (fastforce simp: store_tag_axiom_def writes_mem_val_at_idx_def bind_eq_Some_conv elim!: writes_mem_val.elims)
  show "load_mem_axiom CC ISA is_fetch t"
    using i
    by (fastforce simp: load_mem_axiom_def reads_mem_val_at_idx_def bind_eq_Some_conv elim!: reads_mem_val.elims)
qed

locale Mem_Automaton = Capability_ISA_Fixed_Translation where CC = CC and ISA = ISA
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa" +
  fixes is_fetch :: bool
begin

definition paddr_in_mem_region :: "'cap \<Rightarrow> acctype \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "paddr_in_mem_region c acctype paddr sz =
     (\<exists>vaddr. set (address_range vaddr sz) \<subseteq> get_mem_region CC c \<and>
              translate_address ISA vaddr acctype [] = Some paddr)"

definition has_access_permission :: "'cap \<Rightarrow> acctype \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "has_access_permission c acctype is_cap is_local_cap =
     (case acctype of
        Fetch \<Rightarrow> permits_execute_method CC c
      | Load \<Rightarrow> permits_load_method CC c \<and> (is_cap \<longrightarrow> permits_load_cap_method CC c)
      | Store \<Rightarrow> permits_store_method CC c \<and> (is_cap \<longrightarrow> permits_store_cap_method CC c) \<and>
                 (is_local_cap \<longrightarrow> permits_store_local_cap_method CC c))"

definition authorises_access :: "'cap \<Rightarrow> acctype \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "authorises_access c acctype is_cap is_local_cap paddr sz =
     (is_tagged_method CC c \<and> \<not>is_sealed_method CC c \<and> paddr_in_mem_region c acctype paddr sz \<and>
      has_access_permission c acctype is_cap is_local_cap)"

definition legal_store :: "nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "legal_store sz v tag \<longleftrightarrow> (tag = B0 \<or> tag = B1) \<and> sz = length v"

definition access_enabled :: "('cap, 'regval) axiom_state \<Rightarrow> acctype \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory_byte list \<Rightarrow> bitU \<Rightarrow> bool" where
  "access_enabled s acctype paddr sz v tag =
     ((tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA) \<and>
      (acctype = Fetch \<longrightarrow> tag = B0) \<and>
      (acctype = PTW \<or>
       (\<exists>c' \<in> derivable (accessed_caps s).
          let is_cap = tag \<noteq> B0 in
          let is_local_cap = mem_val_is_local_cap CC ISA v tag \<and> tag = B1 in
          authorises_access c' acctype is_cap is_local_cap paddr sz)))"

lemmas access_enabled_defs = access_enabled_def authorises_access_def paddr_in_mem_region_def
  has_access_permission_def legal_store_def

fun enabled :: "('cap, 'regval) axiom_state \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "enabled s (E_write_mem wk paddr sz v r) =
     (let acctype = if is_translation_event ISA (E_write_mem wk paddr sz v r) then PTW else Store in
      access_enabled s acctype paddr sz v B0 \<and> legal_store sz v B0)"
| "enabled s (E_write_memt wk paddr sz v tag r) =
     (let acctype = if is_translation_event ISA (E_write_memt wk paddr sz v tag r) then PTW else Store in
      access_enabled s acctype paddr sz v tag \<and> legal_store sz v tag)"
| "enabled s (E_read_mem rk paddr sz v) =
     (let acctype =
        if is_translation_event ISA (E_read_mem rk paddr sz v) then PTW else
        if is_fetch then Fetch else
        Load
      in
      access_enabled s acctype paddr sz v B0)"
| "enabled s (E_read_memt rk paddr sz v_tag) =
     (let acctype =
        if is_translation_event ISA (E_read_memt rk paddr sz v_tag) then PTW else
        if is_fetch then Fetch else
        Load
      in
      access_enabled s acctype paddr sz (fst v_tag) (snd v_tag))"
| "enabled s _ = True"

sublocale Cap_Axiom_Automaton where enabled = enabled ..

lemma accepts_store_mem_axiom:
  assumes *: "translation_assms t" and  **: "accepts t"
  shows "store_mem_axiom CC ISA t"
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
  assumes *: "translation_assms t" and  **: "accepts t"
  shows "load_mem_axiom CC ISA is_fetch t"
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
  Mem_Automaton translation_assms CC ISA is_fetch
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and translation_assms :: "'regval event list \<Rightarrow> bool"
    and is_fetch :: bool and ex_traces :: bool +
  fixes ev_assms :: "'regval event \<Rightarrow> bool"
begin

sublocale Cap_Axiom_Assm_Automaton where enabled = enabled and ex_traces = ex_traces
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
    and "translation_assms t"
  shows "store_mem_axiom CC ISA t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA is_fetch t"
  using assms
  by (intro accepts_store_mem_axiom accepts_store_tag_axiom accepts_load_mem_axiom
            traces_enabled_accepts_fromI;
      auto)+

end

locale Mem_Inv_Automaton =
  Mem_Automaton translation_assms CC ISA is_fetch +
  State_Invariant get_regval set_regval invariant inv_regs
  for CC :: "'cap Capability_class" and ISA :: "('cap, 'regval, 'instr, 'e) isa"
    and translation_assms :: "'regval event list \<Rightarrow> bool"
    and is_fetch :: bool and ex_traces :: bool
    and get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
    and invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set"
begin

sublocale Cap_Axiom_Inv_Automaton where enabled = enabled and ex_traces = ex_traces
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
    and "translation_assms t"
  shows "store_mem_axiom CC ISA t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA is_fetch t"
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
