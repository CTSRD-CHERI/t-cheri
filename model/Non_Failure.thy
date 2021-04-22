theory Non_Failure

imports
  "Trace_Assumptions"

begin

abbreviation(input)
  "Failed m tr msg \<equiv> ((m, tr, Fail msg) \<in> Traces)"

definition
  regs_ok :: "(string \<times> (('a \<Rightarrow> bool) \<times> 'b)) list \<Rightarrow> 'a event list \<Rightarrow> bool"
  where
  "regs_ok regs tr = (\<forall>ev \<in> set tr. register_reads_ok (map_option fst o Map.map_of regs) ev)"

lemma regs_ok_append[simp]:
  "regs_ok regs (xs @ ys) = (regs_ok regs xs \<and> regs_ok regs ys)"
  by (auto simp add: regs_ok_def)

lemma Fail_bind_casesE:
  assumes f: "Failed (Sail2_prompt_monad.bind m f) t x"
  assumes early: "\<And>x. Failed m t x \<Longrightarrow> P"
  assumes late: "\<And>x y tr_a tr_b. Run m tr_a x \<Longrightarrow> Failed (f x) tr_b y \<Longrightarrow> t = tr_a @ tr_b \<Longrightarrow> P"
  shows "P"
  apply (rule bind_Traces_cases[OF f])
   apply (case_tac m'', simp_all)
    apply (auto elim: late early dest!: sym[where s="Fail _"])
  done

lemma Fail_ifE:
  assumes "Failed (if b then f else g) t msg"
  obtains "b" and "Failed f t msg" | "\<not>b" and "Failed g t msg"
  using assms by (auto split: if_splits)

lemma Fail_assert_expE:
  assumes "Failed (assert_exp P msg') t msg"
  obtains "\<not> P" and "msg = msg'" and "t = []"
  using assms by (auto simp: assert_exp_def split: if_splits)

lemmas trace_eqD = arg_cong[where f="\<lambda>m. (m, _, _) \<in> Traces", THEN iffD1]

lemmas monad_unfolds = and_boolM_def or_boolM_def Let_def[THEN meta_eq_to_obj_eq]

lemma Failed_impossible:
  "(return x, t, Fail msg) \<in> Traces \<Longrightarrow> P"
  "(throw x, t, Fail msg) \<in> Traces \<Longrightarrow> P"
  by auto

lemmas Fail_elims = Fail_bind_casesE
    Fail_ifE Fail_assert_expE
    Failed_impossible
    monad_unfolds[THEN trace_eqD, elim_format]

named_theorems failureD

lemma read_reg_non_failure:
  "Failed (read_reg r) tr msg \<Longrightarrow> regs_ok regs tr \<Longrightarrow>
    (map_of regs (name r) \<noteq> Some (register_ops_of r))"
  by (auto simp: regs_ok_def
    dest: read_reg_non_failure[where f="map_option fst o map_of regs"])

lemma write_reg_non_failure[failureD]:
  "Failed (write_reg r v) tr msg \<Longrightarrow> False"
  by (auto simp: write_reg_def elim: Traces.cases elim!: T.cases)

method non_failure uses rsimps =
  (determ \<open>auto elim!: Fail_elims dest!: failureD; (auto elim!: Run_elims simp: rsimps)?\<close>)

lemma exhaust_helper:
  "y = max_word \<Longrightarrow> (x \<noteq> y) = (x < y)"
  "x \<noteq> y - 1 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> (x < y) = (x < y - 1)"
  by (auto intro: neq_le_trans dest: inc_le, unat_arith+)

end