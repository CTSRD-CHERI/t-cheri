theory Trace_Assumptions
  imports "Sail.Sail2_state_lemmas" "HOL-Eisbach.Eisbach_Tools"
begin

section \<open>Trivia\<close>

text \<open>TODO: Add this to library\<close>

lemma return_Traces_iff[simp]:
  "(return x, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Done x"
  by (auto simp: return_def)

lemma Run_read_regE:
  assumes "Run (read_reg r) t v"
  obtains (Read) rv where "t = [E_read_reg (name r) rv]" and "of_regval r rv = Some v"
  using assms
  by (auto simp: read_reg_def elim!: Read_reg_TracesE split: option.splits)

lemmas Run_elims = Run_bindE Run_or_boolM_E Run_returnE Run_letE Run_and_boolM_E Run_ifE (*Run_read_regE*)

lemma Run_assert_exp_iff[simp]: "Run (assert_exp c m) t a \<longleftrightarrow> c \<and> t = [] \<and> a = ()"
  by (auto simp: assert_exp_def)

lemma Run_liftR_assert_exp_iff[simp]:
  "Run (liftR (assert_exp c msg :: ('r, unit, 'ex) monad)) t a \<longleftrightarrow> Run (assert_exp c msg :: ('r, unit, 'ex) monad) t a"
  by (auto simp: assert_exp_def liftR_def)

lemma Run_foreachM_appendE:
  assumes "Run (foreachM (xs @ ys) vars body) t vars'"
  obtains txs tys vars''
  where "t = txs @ tys"
    and "Run (foreachM xs vars body) txs vars''"
    and "Run (foreachM ys vars'' body) tys vars'"
proof -
  have "\<exists>txs tys vars''.
           t = txs @ tys \<and>
           Run (foreachM xs vars body) txs vars'' \<and>
           Run (foreachM ys vars'' body) tys vars'"
  proof (use assms in \<open>induction xs arbitrary: vars t\<close>)
    case (Cons x xs)
    then obtain vars'' tx t'
      where tx: "Run (body x vars) tx vars''"
        and t': "Run (foreachM (xs @ ys) vars'' body) t' vars'"
        and t: "t = tx @ t'"
      by (auto elim: Run_bindE)
    from Cons.IH[OF t'] obtain vars''' txs tys
      where "t' = txs @ tys"
        and "Run (foreachM xs vars'' body) txs vars'''"
        and tys: "Run (foreachM ys vars''' body) tys vars'"
      by blast
    then have "Run (foreachM (x # xs) vars body) (tx @ txs) vars'''"
      using tx
      by (auto intro: Traces_bindI)
    then show ?case
      using tys
      unfolding \<open>t = tx @ t'\<close> and \<open>t' = txs @ tys\<close> and append_assoc[symmetric]
      by blast
  qed auto
  then show thesis
    using that
    by blast
qed

lemma Run_foreachM_elim:
  assumes "Run (foreachM xs vars body) t vars'"
    and "\<And>n tl tn tr vars' vars''.
            \<lbrakk>t = tl @ tn @ tr;
             P tl vars';
             Run (body (xs ! n) vars') tn vars'';
             n < length xs\<rbrakk>
            \<Longrightarrow> P (tl @ tn) vars''"
    and "P [] vars"
  shows "P t vars'"
  using assms
proof (use assms in \<open>induction xs arbitrary: t vars' rule: rev_induct\<close>)
  case (snoc x xs)
  then obtain txs tx vars''
    where t: "t = txs @ tx"
      and txs: "Run (foreachM xs vars body) txs vars''"
      and tx: "Run (body x vars'') tx vars'"
    by (elim Run_foreachM_appendE) auto
  then have "P txs vars''"
    using \<open>P [] vars\<close>
    by (intro snoc.IH[OF txs]) (auto simp: nth_append intro!: snoc.prems(2))
  then show ?case
    using t txs tx
    using snoc.prems(2)[where tl = txs and tn = tx and tr = "[]" and n = "length xs"]
    by auto
qed auto

lemma Run_try_catchE:
  assumes "Run (try_catch m h) t a"
  obtains (Run) "Run m t a"
  | (Catch) tm e th where "(m, tm, Exception e) \<in> Traces" and "Run (h e) th a" and "t = tm @ th"
proof (use assms in \<open>cases rule: try_catch_Traces_cases\<close>)
  case (NoEx m')
  then show ?thesis
    by (cases "(m', h)" rule: try_catch.cases) (auto elim!: Run Catch)
next
  case (Ex tm ex th)
  show ?thesis using Catch[OF Ex] .
qed

lemma throw_Traces_iff[simp]:
  "(throw e, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Exception e"
  by (auto simp: throw_def)

lemma early_return_Traces_iff[simp]:
  "(early_return a, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Exception (Inl a)"
  by (auto simp: early_return_def)

lemma Run_catch_early_returnE:
  assumes "Run (catch_early_return m) t a"
  obtains (Run) "Run m t a"
  | (Early) "(m, t, Exception (Inl a)) \<in> Traces"
  using assms
  unfolding catch_early_return_def
  by (elim Run_try_catchE) (auto split: sum.splits)

section \<open>(Conditionally) deterministic monadic expressions\<close>

definition "determ_exp_if P m c \<equiv> (\<forall>t a. Run m t a \<and> P t \<longrightarrow> a = c)"
definition "prefix_closed P \<equiv> (\<forall>t1 t2. P (t1 @ t2) \<longrightarrow> P t1)"

lemma Run_bind_determ_exp_ifE:
  assumes "prefix_closed P"
    and "determ_exp_if P m c"
    and "Run (m \<bind> f) t a"
    and "P t"
  obtains tm tf where "Run m tm c" and "Run (f c) tf a" and "t = tm @ tf"
  using assms
  by (elim Run_bindE) (auto simp: determ_exp_if_def prefix_closed_def)

abbreviation "determ_exp \<equiv> determ_exp_if (\<lambda>_. True)"

lemma Run_bind_determ_expE:
  assumes "determ_exp m c"
    and "Run (m \<bind> f) t a"
  obtains tm tf where "Run m tm c" and "Run (f c) tf a" and "t = tm @ tf"
  using assms
  by (elim Run_bindE) (auto simp: determ_exp_if_def)

section \<open>Assumptions about register reads and writes\<close>

definition "no_reg_writes_to Rs m \<equiv> (\<forall>t m' r v. (m, t, m') \<in> Traces \<and> r \<in> Rs \<longrightarrow> E_write_reg r v \<notin> set t)"
definition "runs_no_reg_writes_to Rs m \<equiv> (\<forall>t a r v. Run m t a \<and> r \<in> Rs \<longrightarrow> E_write_reg r v \<notin> set t)"

named_theorems no_reg_writes_toI
named_theorems runs_no_reg_writes_toI

lemma no_reg_writes_to_empty[intro, simp]:
  "no_reg_writes_to {} m"
  "runs_no_reg_writes_to {} m"
  by (auto simp: no_reg_writes_to_def runs_no_reg_writes_to_def)

lemma no_reg_writes_runs_no_reg_writes:
  "no_reg_writes_to Rs m \<Longrightarrow> runs_no_reg_writes_to Rs m"
  by (auto simp: no_reg_writes_to_def runs_no_reg_writes_to_def)

lemma no_reg_writes_to_bindI[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m" and "\<And>t a. Run m t a \<Longrightarrow> no_reg_writes_to Rs (f a)"
  shows "no_reg_writes_to Rs (m \<bind> f)"
  using assms
  by (auto simp: no_reg_writes_to_def elim: bind_Traces_cases)

lemma no_reg_writes_to_bindI_ignore_left:
  assumes "no_reg_writes_to Rs m" and "\<And>a. no_reg_writes_to Rs (f a)"
  shows "no_reg_writes_to Rs (m \<bind> f)"
  using assms
  by (intro no_reg_writes_to_bindI)

lemma runs_no_reg_writes_to_bindI[intro, simp, runs_no_reg_writes_toI]:
  assumes "runs_no_reg_writes_to Rs m" and "\<And>t a. Run m t a \<Longrightarrow> runs_no_reg_writes_to Rs (f a)"
  shows "runs_no_reg_writes_to Rs (m \<bind> f)"
  using assms
  by (auto simp: runs_no_reg_writes_to_def elim: Run_bindE)

lemma runs_no_reg_writes_to_bindI_ignore_left:
  assumes "runs_no_reg_writes_to Rs m" and "\<And>a. runs_no_reg_writes_to Rs (f a)"
  shows "runs_no_reg_writes_to Rs (m \<bind> f)"
  using assms
  by (intro runs_no_reg_writes_to_bindI)

lemma no_reg_writes_to_return[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (return a)"
  by (auto simp: no_reg_writes_to_def)

lemma no_reg_writes_to_throw[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (throw e)"
  by (auto simp: no_reg_writes_to_def)

lemma no_reg_writes_to_Fail[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (Fail msg)"
  by (auto simp: no_reg_writes_to_def)

lemma no_reg_writes_to_try_catchI[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m" and "\<And>e. no_reg_writes_to Rs (h e)"
  shows "no_reg_writes_to Rs (try_catch m h)"
  using assms
  by (auto simp: no_reg_writes_to_def elim!: try_catch_Traces_cases)

lemma no_reg_writes_to_catch_early_returnI[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m"
  shows "no_reg_writes_to Rs (catch_early_return m)"
  using assms
  by (auto simp: catch_early_return_def split: sum.splits)

lemma no_reg_writes_to_early_return[intro, simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (early_return a)"
  by (auto simp: early_return_def)

lemma no_reg_writes_to_liftR_I[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m"
  shows "no_reg_writes_to Rs (liftR m)"
  using assms
  by (auto simp: liftR_def)

lemma no_reg_writes_to_let[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (f x) \<Longrightarrow> no_reg_writes_to Rs (let a = x in f a)"
  by auto

lemma runs_no_reg_writes_to_let[simp, runs_no_reg_writes_toI]:
  "runs_no_reg_writes_to Rs (f x) \<Longrightarrow> runs_no_reg_writes_to Rs (let a = x in f a)"
  by auto

lemma no_reg_writes_to_if[simp, no_reg_writes_toI]:
  assumes "c \<Longrightarrow> no_reg_writes_to Rs m1" and "\<not>c \<Longrightarrow> no_reg_writes_to Rs m2"
  shows "no_reg_writes_to Rs (if c then m1 else m2)"
  using assms
  by auto

lemma runs_no_reg_writes_to_if[simp, runs_no_reg_writes_toI]:
  assumes "c \<Longrightarrow> runs_no_reg_writes_to Rs m1" and "\<not>c \<Longrightarrow> runs_no_reg_writes_to Rs m2"
  shows "runs_no_reg_writes_to Rs (if c then m1 else m2)"
  using assms
  by auto

lemma no_reg_writes_to_case_prod[intro, simp, no_reg_writes_toI]:
  assumes "\<And>x y. no_reg_writes_to Rs (f x y)"
  shows "no_reg_writes_to Rs (case z of (x, y) \<Rightarrow> f x y)"
  using assms
  by (cases z) auto

lemma runs_no_reg_writes_to_case_prod[intro, simp, runs_no_reg_writes_toI]:
  assumes "\<And>x y. runs_no_reg_writes_to Rs (f x y)"
  shows "runs_no_reg_writes_to Rs (case z of (x, y) \<Rightarrow> f x y)"
  using assms
  by (cases z) auto

lemma no_reg_writes_to_case_bool[intro, simp, no_reg_writes_toI]:
  assumes "z \<Longrightarrow> no_reg_writes_to Rs m1" and "\<not>z \<Longrightarrow> no_reg_writes_to Rs m2"
  shows "no_reg_writes_to Rs (case z of True \<Rightarrow> m1 | False \<Rightarrow> m2)"
  using assms
  by (cases z) auto

lemma runs_no_reg_writes_to_case_bool[intro, simp, runs_no_reg_writes_toI]:
  assumes "z \<Longrightarrow> runs_no_reg_writes_to Rs m1" and "\<not>z \<Longrightarrow> runs_no_reg_writes_to Rs m2"
  shows "runs_no_reg_writes_to Rs (case z of True \<Rightarrow> m1 | False \<Rightarrow> m2)"
  using assms
  by (cases z) auto

lemma no_reg_writes_to_choose_bool[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (choose_bool desc)"
  by (auto simp: choose_bool_def no_reg_writes_to_def elim: Traces_cases)

lemma no_reg_writes_to_undefined_bool[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (undefined_bool ())"
  by (auto simp: undefined_bool_def)

lemma no_reg_writes_to_foreachM[simp, no_reg_writes_toI]:
  assumes "\<And>x vars. no_reg_writes_to Rs (body x vars)"
  shows "no_reg_writes_to Rs (foreachM xs vars body)"
  using assms
  by (induction xs vars body rule: foreachM.induct) auto

lemma runs_no_reg_writes_to_foreachM[simp, runs_no_reg_writes_toI]:
  assumes "\<And>x vars. runs_no_reg_writes_to Rs (body x vars)"
  shows "runs_no_reg_writes_to Rs (foreachM xs vars body)"
  using assms
  by (induction xs vars body rule: foreachM.induct) (auto intro: no_reg_writes_runs_no_reg_writes)

lemma no_reg_writes_to_bool_of_bitU_nondet[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (bool_of_bitU_nondet b)"
  by (cases b) (auto simp: bool_of_bitU_nondet_def)

lemma no_reg_writes_to_bool_of_bitU_fail[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (bool_of_bitU_fail b)"
  by (cases b) (auto simp: bool_of_bitU_fail_def)

lemma no_reg_writes_to_and_boolM[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m1" and "no_reg_writes_to Rs m2"
  shows "no_reg_writes_to Rs (and_boolM m1 m2)"
  using assms
  by (auto simp: and_boolM_def)

lemma no_reg_writes_to_or_boolM[intro, simp, no_reg_writes_toI]:
  assumes "no_reg_writes_to Rs m1" and "no_reg_writes_to Rs m2"
  shows "no_reg_writes_to Rs (or_boolM m1 m2)"
  using assms
  by (auto simp: or_boolM_def)

lemma no_reg_writes_to_assert_exp[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (assert_exp c m)"
  by (auto simp: assert_exp_def no_reg_writes_to_def)

lemma no_reg_writes_to_exit[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (exit0 ())"
  by (auto simp: exit0_def no_reg_writes_to_def)

lemma no_reg_writes_to_read_reg[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (read_reg r)"
  by (auto simp: no_reg_writes_to_def read_reg_def elim: Read_reg_TracesE split: option.splits)

lemma no_reg_writes_to_write_reg[simp, no_reg_writes_toI]:
  assumes "name r \<notin> Rs"
  shows "no_reg_writes_to Rs (write_reg r v)"
  using assms
  by (auto simp: no_reg_writes_to_def write_reg_def elim!: Write_reg_TracesE)

lemma no_reg_writes_to_read_mem_bytes[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (read_mem_bytes BC BC' rk addr bytes)"
  by (auto simp: read_mem_bytes_def no_reg_writes_to_def maybe_fail_def
           elim: Traces_cases split: option.splits)

lemma no_reg_writes_to_read_mem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (read_mem BC BC' rk addr_length addr bytes)"
  by (auto simp: read_mem_def split: option.splits)

lemma no_reg_writes_to_read_memt_bytes[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (read_memt_bytes BCa BCb rk addr sz)"
  unfolding read_memt_bytes_def maybe_fail_def
  by (auto simp: no_reg_writes_to_def split: option.splits elim: Traces_cases)

lemma no_reg_writes_to_read_memt[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (read_memt BCa BCb rk addr sz)"
  by (auto simp: read_memt_def split: option.splits)

lemma no_reg_writes_to_write_mem_ea[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (write_mem_ea BC wk addr_length addr bytes)"
  by (auto simp: write_mem_ea_def no_reg_writes_to_def maybe_fail_def split: option.splits elim: Traces_cases)

lemma no_reg_writes_to_write_mem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (write_mem BC BC' wk addr_length addr bytes value)"
  by (auto simp: write_mem_def no_reg_writes_to_def split: option.splits elim: Traces_cases)

lemma no_reg_writes_to_write_memt[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (write_memt BC BC' wk addr bytes value tag)"
  by (auto simp: write_memt_def no_reg_writes_to_def split: option.splits elim: Traces_cases)

lemma no_reg_writes_to_genlistM[simp, no_reg_writes_toI]:
  assumes "\<And>i. no_reg_writes_to Rs (f i)"
  shows "no_reg_writes_to Rs (genlistM f n)"
  using assms
  by (auto simp: genlistM_def)

lemma no_reg_writes_to_choose_bools[simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (choose_bools desc n)"
  by (auto simp: choose_bools_def)

lemma no_reg_writes_to_chooseM[simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (chooseM desc xs)"
  by (auto simp: chooseM_def split: option.splits)

lemma no_reg_writes_to_internal_pick[simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (internal_pick xs)"
  by (auto simp: internal_pick_def)

lemma no_reg_writes_to_bools_of_bits_nondet[simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (bools_of_bits_nondet bits)"
  by (auto simp: bools_of_bits_nondet_def)

lemma no_reg_writes_to_of_bits_nondet[simp, no_reg_writes_toI]:
  shows "no_reg_writes_to Rs (of_bits_nondet BC bits)"
  by (auto simp: of_bits_nondet_def)

definition
  bind_ignore :: "('rv, 'a, 'e) monad \<Rightarrow> ('rv, 'b, 'e) monad \<Rightarrow> ('rv, 'b, 'e) monad"
  where
  "bind_ignore f g = Sail2_prompt_monad.bind f (\<lambda>_. g)"

lemma bind_ignored_after_one:
  "(m1 \<bind> (\<lambda>x. bind_ignore (m2 x) m3)) = (bind_ignore (m1 \<bind> m2) m3)"
  by (simp add: bind_ignore_def)

lemmas fold_bind_ignore = bind_ignored_after_one bind_ignore_def[symmetric]

lemma fold_trio_bind_ignore:
  "(m1 \<bind> (\<lambda>x. m2 x \<bind> (\<lambda>y. m3))) = (bind_ignore (m1 \<bind> m2) m3)"
  by (simp add: bind_ignore_def)

lemma no_reg_writes_to_bind_ignore[no_reg_writes_toI]:
  "no_reg_writes_to Rs m1 \<Longrightarrow> no_reg_writes_to Rs m2 \<Longrightarrow> no_reg_writes_to Rs (bind_ignore m1 m2)"
  by (simp add: bind_ignore_def)

lemmas no_reg_write_builtins =
  no_reg_writes_to_return no_reg_writes_to_throw no_reg_writes_to_Fail
  no_reg_writes_to_early_return no_reg_writes_to_assert_exp
  no_reg_writes_to_read_reg no_reg_writes_to_chooseM no_reg_writes_to_internal_pick
  no_reg_writes_to_choose_bool no_reg_writes_to_undefined_bool
  no_reg_writes_to_bool_of_bitU_nondet no_reg_writes_to_bools_of_bits_nondet
  no_reg_writes_to_bool_of_bitU_fail
  no_reg_writes_to_of_bits_nondet no_reg_writes_to_choose_bools no_reg_writes_to_exit
  no_reg_writes_to_read_mem_bytes no_reg_writes_to_read_mem
  no_reg_writes_to_read_memt_bytes no_reg_writes_to_read_memt
  no_reg_writes_to_write_mem_ea no_reg_writes_to_write_mem no_reg_writes_to_write_memt

method no_reg_writes_toI uses simp intro =
  (intro intro runs_no_reg_writes_toI no_reg_writes_runs_no_reg_writes no_reg_writes_toI conjI impI allI;
    (erule contra_subsetD subset_trans;
      simp(no_asm) only: simp register_ref.simps insert_subset empty_subsetI insert_iff
                         empty_iff simp_thms list.simps)?;
   auto simp: simp split del: if_split split: option.splits)

abbreviation "exp_fails m \<equiv> (\<forall>t a. \<not>Run m t a)"

lemma exp_fails_bind_iff[simp]:
  "exp_fails (m \<bind> f) \<longleftrightarrow> exp_fails m \<or> (\<forall>t a. Run m t a \<longrightarrow> exp_fails (f a))"
  by (auto elim!: Run_bindE intro: Traces_bindI)

lemma exp_fails_if_then_else:
  assumes "exp_fails m1"
  shows "Run (if c then m1 else m2) t a \<longleftrightarrow> \<not>c \<and> Run m2 t a"
  using assms
  by auto

locale Register_State =
  fixes get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
begin

fun updates_regs :: "string set \<Rightarrow> 'regval trace \<Rightarrow> 'regstate \<Rightarrow> 'regstate option" where
  "updates_regs R [] s = Some s"
| "updates_regs R (E_write_reg r v # t) s =
     (if r \<in> R
      then Option.bind (set_regval r v s) (updates_regs R t)
      else updates_regs R t s)"
| "updates_regs R (_ # t) s = updates_regs R t s"

fun reads_regs_from :: "string set \<Rightarrow> 'regval trace \<Rightarrow> 'regstate \<Rightarrow> bool" where
  "reads_regs_from R [] s = True"
| "reads_regs_from R (E_read_reg r v # t) s =
     (if r \<in> R
      then get_regval r s = Some v \<and> reads_regs_from R t s
      else reads_regs_from R t s)"
| "reads_regs_from R (E_write_reg r v # t) s =
     (if r \<in> R
      then (case set_regval r v s of Some s' \<Rightarrow> reads_regs_from R t s' | None \<Rightarrow> False)
      else reads_regs_from R t s)"
| "reads_regs_from R (_ # t) s = reads_regs_from R t s"

lemma reads_regs_from_updates_regs_Some:
  assumes "reads_regs_from R t s"
  obtains s' where "updates_regs R t s = Some s'"
  using assms
  by (induction R t s rule: reads_regs_from.induct) (auto split: if_splits option.splits)

named_theorems regstate_simp

lemma updates_regs_append_iff[regstate_simp]:
  "updates_regs R (t @ t') s = Option.bind (updates_regs R t s) (updates_regs R t')"
  by (induction R t s rule: updates_regs.induct) (auto split: bind_splits)

lemma reads_regs_from_append_iff[regstate_simp]:
  "reads_regs_from R (t @ t') s \<longleftrightarrow> (reads_regs_from R t s \<and> reads_regs_from R t' (the (updates_regs R t s)))"
  by (induction R t s rule: reads_regs_from.induct) (auto split: option.splits)

lemma reads_regs_from_appendE_simp:
  assumes "reads_regs_from Rs t regs" and "t = t1 @ t2"
    and "the (updates_regs Rs t1 regs) = regs'"
  obtains "reads_regs_from Rs t1 regs" and "reads_regs_from Rs t2 regs'"
  using assms
  by (auto simp: reads_regs_from_append_iff)

lemma no_reg_writes_to_updates_regs_inv[simp]:
  assumes "(m, t, m') \<in> Traces"
    and "no_reg_writes_to Rs m"
  shows "updates_regs Rs t s = Some s"
  using assms
proof -
  have "\<forall>r \<in> Rs. \<forall>v. E_write_reg r v \<notin> set t"
    using assms
    by (auto simp: no_reg_writes_to_def)
  then show "updates_regs Rs t s = Some s"
    by (induction Rs t s rule: updates_regs.induct) auto
qed

lemma no_reg_writes_to_updates_regsE:
  assumes "(m, t, m') \<in> Traces"
    and "no_reg_writes_to Rs m"
  obtains "updates_regs Rs t s = Some s"
  using assms
  by auto

lemma Run_choose_bool_updates_regs[regstate_simp]:
  assumes "Run (choose_bool desc) t b"
  shows "updates_regs Rs t regs = Some regs"
  using assms
  by (auto simp: choose_bool_def elim!: Traces_cases[where t = t])

lemma Run_choose_bools_updates_regs[regstate_simp]:
  assumes "Run (choose_bools desc n) t b"
  shows "updates_regs Rs t regs = Some regs"
  using assms
  by (auto simp: choose_bools_def genlistM_def regstate_simp elim!: Run_foreachM_elim Run_bindE)

lemma Run_undefined_bool_updates_regs[regstate_simp]:
  assumes "Run (undefined_bool u) t b"
  shows "updates_regs Rs t regs = Some regs"
  using assms
  unfolding undefined_bool_def
  by (elim Run_choose_bool_updates_regs)

lemma Run_internal_pick_updates_regs[regstate_simp]:
  assumes "Run (internal_pick xs) t a"
  shows "updates_regs Rs t regs = Some regs"
  using assms
  by (auto simp: internal_pick_def chooseM_def regstate_simp elim!: Run_elims split: option.splits)

named_theorems RunE

method RunE uses elim =
  (match premises in R[thin]: \<open>Run m t a\<close> and regs[thin]: "reads_regs_from Rs t regs" for m t a Rs regs \<Rightarrow>
     \<open>match elim RunE in E: \<open>R' \<Longrightarrow> regs' \<Longrightarrow> _\<close> for R' regs' \<Rightarrow>
        \<open>match (\<open>Run m t a\<close>) in R' \<Rightarrow>
           \<open>match (\<open>reads_regs_from Rs t regs\<close>) in regs' \<Rightarrow>
              \<open>rule E[OF R regs]; (RunE elim: elim)?\<close>\<close>\<close>\<close>)

end

section \<open>State invariants\<close>

locale State_Invariant = Register_State get_regval set_regval
  for get_regval :: "string \<Rightarrow> 'regstate \<Rightarrow> 'regval option"
    and set_regval :: "string \<Rightarrow> 'regval \<Rightarrow> 'regstate \<Rightarrow> 'regstate option"
+ fixes invariant :: "'regstate \<Rightarrow> bool" and inv_regs :: "register_name set"
begin

definition
  "Run_inv m t a regs \<equiv> Run m t a \<and> reads_regs_from inv_regs t regs \<and> invariant regs"

definition trace_preserves_invariant :: "'regval trace \<Rightarrow> bool" where
  "trace_preserves_invariant t \<equiv>
     (\<forall>s. invariant s \<and> reads_regs_from inv_regs t s \<longrightarrow> invariant (the (updates_regs inv_regs t s)))"

lemma trace_preserves_invariantE:
  assumes "trace_preserves_invariant t" and "reads_regs_from inv_regs t s" and "invariant s"
  obtains s' where "updates_regs inv_regs t s = Some s'" and "invariant s'"
  using assms
  by (fastforce simp: trace_preserves_invariant_def elim: reads_regs_from_updates_regs_Some)

lemma trace_preserves_invariant_appendI:
  assumes t1: "trace_preserves_invariant t1" and t2: "trace_preserves_invariant t2"
  shows "trace_preserves_invariant (t1 @ t2)"
  using t2
  by (auto simp: trace_preserves_invariant_def regstate_simp elim: trace_preserves_invariantE[OF t1])

definition traces_preserve_invariant :: "('regval, 'a, 'e) monad \<Rightarrow> bool" where
  "traces_preserve_invariant m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> trace_preserves_invariant t)"

definition runs_preserve_invariant :: "('regval, 'a, 'e) monad \<Rightarrow> bool" where
  "runs_preserve_invariant m \<equiv> (\<forall>t a. Run m t a \<longrightarrow> trace_preserves_invariant t)"

definition exceptions_preserve_invariant :: "('regval, 'a, 'e) monad \<Rightarrow> bool" where
  "exceptions_preserve_invariant m \<equiv> (\<forall>t e. (m, t, Exception e) \<in> Traces \<longrightarrow> trace_preserves_invariant t)"

lemma traces_runs_preserve_invariantI:
  assumes "traces_preserve_invariant m"
  shows "runs_preserve_invariant m"
  using assms
  by (auto simp: traces_preserve_invariant_def runs_preserve_invariant_def)

lemma traces_exceptions_preserve_invariantI:
  assumes "traces_preserve_invariant m"
  shows "exceptions_preserve_invariant m"
  using assms
  by (auto simp: traces_preserve_invariant_def exceptions_preserve_invariant_def)

lemma traces_preserve_invariantE:
  assumes "traces_preserve_invariant m"
    and "(m, t, m') \<in> Traces" and "invariant s" and "reads_regs_from inv_regs t s"
  obtains s' where "updates_regs inv_regs t s = Some s'" and "invariant s'"
  using assms
  by (auto simp: traces_preserve_invariant_def elim: trace_preserves_invariantE)

lemma runs_preserve_invariantE:
  assumes "runs_preserve_invariant m"
    and "Run m t a" and "invariant s" and "reads_regs_from inv_regs t s"
  obtains s' where "updates_regs inv_regs t s = Some s'" and "invariant s'"
  using assms
  by (auto simp: runs_preserve_invariant_def elim: trace_preserves_invariantE)

lemma Run_inv_bindE:
  assumes "Run_inv (m \<bind> f) t a regs" and "runs_preserve_invariant m"
  obtains tm am tf where "t = tm @ tf" and "Run_inv m tm am regs"
    and "Run_inv (f am) tf a (the (updates_regs inv_regs tm regs))"
proof -
  from assms
  obtain tm am tf
    where t: "t = tm @ tf" and tm: "Run m tm am" and tf: "Run (f am) tf a"
      and regs: "reads_regs_from inv_regs tm regs"
      and regs': "reads_regs_from inv_regs tf (the (updates_regs inv_regs tm regs))"
      and inv: "invariant regs"
    using assms unfolding Run_inv_def
    by (auto simp: regstate_simp elim!: Run_bindE)
  moreover obtain regs' where regs': "updates_regs inv_regs tm regs = Some regs'" and inv': "invariant regs'"
    using assms tm inv regs
    by (elim runs_preserve_invariantE)
  ultimately show thesis
    using that
    unfolding Run_inv_def
    by auto
qed

named_theorems preserves_invariantI
named_theorems trace_preserves_invariantI

lemma no_reg_writes_trace_preserves_invariantI:
  assumes "no_reg_writes_to inv_regs m"
    and "(m, t, m') \<in> Traces"
  shows "trace_preserves_invariant t"
  using assms
  by (auto simp: trace_preserves_invariant_def)

lemma no_reg_writes_traces_preserve_invariantI:
  assumes "no_reg_writes_to inv_regs m"
  shows "traces_preserve_invariant m"
  using assms
  by (auto simp: traces_preserve_invariant_def intro: no_reg_writes_trace_preserves_invariantI)

(*method preserves_invariantI uses simp elim =
  (auto simp: simp intro!: preserves_invariantI elim!: elim
        intro: no_reg_writes_traces_preserve_invariantI trace_preserves_invariant_appendI
        intro: no_reg_writes_traces_preserve_invariantI[THEN traces_runs_preserve_invariantI]
        intro: no_reg_writes_traces_preserve_invariantI[THEN traces_exceptions_preserve_invariantI]
        split: option.splits sum.splits)*)

method preserves_invariantI uses intro simp elim =
  (intro intro preserves_invariantI conjI allI impI traces_runs_preserve_invariantI traces_exceptions_preserve_invariantI;
   auto simp: simp elim!: elim)

lemma traces_preserve_invariant_bindI[preserves_invariantI]:
  assumes m: "traces_preserve_invariant m"
    and f: "\<And>s t a. Run_inv m t a s \<Longrightarrow> traces_preserve_invariant (f a)"
  shows "traces_preserve_invariant (m \<bind> f)"
proof -
  { fix s t m'
    assume "(m \<bind> f, t, m') \<in> Traces" and s: "invariant s" and regs: "reads_regs_from inv_regs t s"
    then have "invariant (the (updates_regs inv_regs t s))"
    proof (cases rule: bind_Traces_cases)
      case (Left m'')
      with m s regs show ?thesis
        by (auto simp: traces_preserve_invariant_def trace_preserves_invariant_def)
    next
      case (Bind tm am tf)
      then obtain s'
        where regs': "reads_regs_from inv_regs tm s"
          and s': "updates_regs inv_regs tm s = Some s'"
        using regs
        by (auto simp: regstate_simp elim: reads_regs_from_updates_regs_Some)
      then have "invariant s'" and "Run_inv m tm am s"
        using s m \<open>Run m tm am\<close>
        by (fastforce simp: traces_preserve_invariant_def trace_preserves_invariant_def Run_inv_def)+
      then show ?thesis
        using Bind s' regs f[OF \<open>Run_inv m tm am s\<close>]
        by (auto simp: traces_preserve_invariant_def trace_preserves_invariant_def regstate_simp)
    qed
  }
  then show ?thesis
    by (simp add: traces_preserve_invariant_def trace_preserves_invariant_def)
qed

lemma runs_preserve_invariant_bindI[preserves_invariantI]:
  assumes "runs_preserve_invariant m" and "\<And>t a. Run m t a \<Longrightarrow> runs_preserve_invariant (f a)"
  shows "runs_preserve_invariant (m \<bind> f)"
  using assms
  by (fastforce simp: runs_preserve_invariant_def elim!: Run_bindE intro: trace_preserves_invariant_appendI)

lemma runs_preserve_invariant_try_catchI[preserves_invariantI]:
  assumes "runs_preserve_invariant m"
    and "exceptions_preserve_invariant m"
    and "\<And>t e. (m, t, Exception e) \<in> Traces \<Longrightarrow> runs_preserve_invariant (h e)"
  shows "runs_preserve_invariant (try_catch m h)"
  using assms
  by (fastforce simp: runs_preserve_invariant_def exceptions_preserve_invariant_def
                elim!: Run_try_catchE intro: trace_preserves_invariant_appendI)

lemma preserves_invariant_case_sum[preserves_invariantI]:
  assumes "\<And>a. traces_preserve_invariant (f a)" and "\<And>b. traces_preserve_invariant (g b)"
  shows "traces_preserve_invariant (case x of Inl a \<Rightarrow> f a | Inr b \<Rightarrow> g b)"
  using assms
  by (auto split: sum.splits)

lemma preserves_invariant_case_option[preserves_invariantI]:
  assumes "\<And>a. traces_preserve_invariant (f a)" and "traces_preserve_invariant g"
  shows "traces_preserve_invariant (case x of Some a \<Rightarrow> f a | None \<Rightarrow> g)"
  using assms
  by (auto split: option.splits)

lemma preserves_invariant_case_prod[preserves_invariantI]:
  assumes "\<And>x y. traces_preserve_invariant (f x y)"
  shows "traces_preserve_invariant (case z of (x, y) \<Rightarrow> f x y)"
  using assms
  by auto

lemmas no_reg_write_builtins_preserve_invariant[preserves_invariantI] =
  no_reg_write_builtins[THEN no_reg_writes_traces_preserve_invariantI]

lemma preserves_invariant_if[preserves_invariantI]:
  assumes "c \<Longrightarrow> traces_preserve_invariant m1" and "\<not>c \<Longrightarrow> traces_preserve_invariant m2"
  shows "traces_preserve_invariant (if c then m1 else m2)"
  using assms
  by auto

lemma preserves_invariant_try_catch[preserves_invariantI]:
  assumes "traces_preserve_invariant m"
    and "\<And>t e. (m, t, Exception e) \<in> Traces \<Longrightarrow> traces_preserve_invariant (h e)"
  shows "traces_preserve_invariant (try_catch m h)"
  using assms
  by (fastforce simp: traces_preserve_invariant_def elim!: try_catch_Traces_cases
                intro: trace_preserves_invariant_appendI)

lemma preserves_invariant_catch_early_return[preserves_invariantI]:
  assumes "traces_preserve_invariant m"
  shows "traces_preserve_invariant (catch_early_return m)"
  using assms
  by (auto simp: catch_early_return_def intro: preserves_invariantI)

lemma runs_preserve_invariant_catch_early_returnI[preserves_invariantI]:
  assumes "runs_preserve_invariant m"
    and "exceptions_preserve_invariant m"
  shows "runs_preserve_invariant (catch_early_return m)"
  using assms
  unfolding catch_early_return_def
  by (auto intro!: preserves_invariantI no_reg_write_builtins_preserve_invariant[THEN traces_runs_preserve_invariantI] split: sum.splits)

lemma preserves_invariant_liftR[preserves_invariantI]:
  assumes "traces_preserve_invariant m"
  shows "traces_preserve_invariant (liftR m)"
  using assms
  by (auto simp: liftR_def intro: preserves_invariantI)

lemma Nil_preserves_invariant[intro, simp]:
  "trace_preserves_invariant []"
  by (auto simp: trace_preserves_invariant_def)

lemma preserves_invariant_and_boolM[preserves_invariantI]:
  assumes "traces_preserve_invariant m1" and "traces_preserve_invariant m2"
  shows "traces_preserve_invariant (and_boolM m1 m2)"
  using assms
  by (auto simp: and_boolM_def intro: preserves_invariantI)

lemma preserves_invariant_or_boolM[preserves_invariantI]:
  assumes "traces_preserve_invariant m1" and "traces_preserve_invariant m2"
  shows "traces_preserve_invariant (or_boolM m1 m2)"
  using assms
  by (auto simp: or_boolM_def intro: preserves_invariantI)

lemma preserves_invariant_let[preserves_invariantI]:
  assumes "traces_preserve_invariant (f y)"
  shows "traces_preserve_invariant (let x = y in f x)"
  using assms
  by auto

lemma runs_preserve_invariant_foreachM[preserves_invariantI]:
  assumes "\<And>x vars. runs_preserve_invariant (body x vars)"
  shows "runs_preserve_invariant (foreachM xs vars body)"
  using assms
  by (induction xs arbitrary: vars) (auto intro: preserves_invariantI traces_runs_preserve_invariantI)

lemma preserves_invariant_foreachM[preserves_invariantI]:
  assumes "\<And>x vars. traces_preserve_invariant (body x vars)"
  shows "traces_preserve_invariant (foreachM xs vars body)"
  using assms
  by (induction xs arbitrary: vars) (auto intro: preserves_invariantI)

(*lemma reads_regs_from_append_invE_simp:
  assumes "reads_regs_from inv_regs t regs" and "t = t1 @ t2" and "Run m t1 a"
    and "invariant regs" and "runs_preserve_invariant m"
    and "reads_regs_from inv_regs t1 regs \<Longrightarrow> the (updates_regs inv_regs t1 regs) = regs'"
  obtains "reads_regs_from inv_regs t1 regs" and "reads_regs_from inv_regs t2 regs'" and "invariant regs'"
  using assms
  by (auto simp: regstate_simp elim: runs_preserve_invariantE)*)

end

subsection \<open>Deterministic expressions\<close>

context State_Invariant
begin

definition "Traces_inv regs \<equiv> {(m, t, m') | m t m'. (m, t, m') \<in> Traces \<and> reads_regs_from inv_regs t regs \<and> invariant regs \<and> final m'}"
definition "determ_traces m \<equiv> (\<forall>t1 m1' regs1 t2 m2' regs2. (m, t1, m1') \<in> Traces_inv regs1 \<and> (m, t2, m2') \<in> Traces_inv regs2 \<longrightarrow> m1' = m2')"
definition "determ_runs m \<equiv> (\<forall>t1 a1 regs1 t2 a2 regs2. Run_inv m t1 a1 regs1 \<and> Run_inv m t2 a2 regs2 \<longrightarrow> a1 = a2)"
definition "the_outcome m \<equiv> (THE m'. \<exists>t regs. (m, t, m') \<in> Traces_inv regs)"
definition "the_result m \<equiv> (THE a. \<exists>t regs. Run_inv m t a regs)"

lemma in_Traces_inv_iff:
  "(m, t, m') \<in> Traces_inv regs \<longleftrightarrow> (m, t, m') \<in> Traces \<and> reads_regs_from inv_regs t regs \<and> invariant regs \<and> final m'"
  by (auto simp: Traces_inv_def)

lemma Run_inv_iff_Traces_inv:
  "Run_inv m t a regs \<longleftrightarrow> (m, t, Done a) \<in> Traces_inv regs"
  unfolding Run_inv_def in_Traces_inv_iff
  by (auto simp: final_def)

lemma determ_tracesI:
  assumes "\<And>t m'' regs. (m, t, m'') \<in> Traces_inv regs \<Longrightarrow> m'' = m'"
  shows "determ_traces m"
  using assms
  unfolding determ_traces_def
  by blast

lemma determ_runsI:
  assumes "\<And>t a regs. Run_inv m t a regs \<Longrightarrow> a = c"
  shows "determ_runs m"
  using assms
  unfolding determ_runs_def
  by blast

named_theorems determ

lemma determ_the_outcome_eq:
  assumes "determ_traces m" and "(m, t, m') \<in> Traces_inv regs"
  shows "the_outcome m = m'"
  using assms
  unfolding the_outcome_def determ_traces_def in_Traces_inv_iff
  by blast

lemma determ_the_result_eq:
  assumes "determ_runs m" and "Run_inv m t a regs"
  shows "the_result m = a"
  using assms
  unfolding the_result_def determ_runs_def
  by blast

lemma determ_traces_runs:
  assumes "determ_traces m"
  shows "determ_runs m"
  using assms
  unfolding determ_traces_def determ_runs_def Run_inv_iff_Traces_inv
  by blast

lemma determ_runs_return[determ]: "determ_runs (return a)"
  by (auto simp: determ_runs_def Run_inv_def)

lemma determ_traces_return[determ]: "determ_traces (return a)"
  by (auto simp: determ_traces_def in_Traces_inv_iff)

lemma determ_traces_throw[determ]: "determ_traces (throw e)"
  by (auto simp: determ_traces_def in_Traces_inv_iff)

lemma determ_runs_bindI:
  assumes "determ_runs m" and "determ_runs (f (the_result m))" and "runs_preserve_invariant m"
  shows "determ_runs (m \<bind> f)"
  using assms
  by (intro determ_runsI[where c = "the_result (f (the_result m))"])
     (auto elim!: Run_inv_bindE simp: determ_the_result_eq)

lemma final_simps[intro, simp]:
  "final (Exception e)"
  "final (Fail msg)"
  by (auto simp: final_def)

lemma runs_preserve_invariant_Run_invariant[simp]:
  assumes "runs_preserve_invariant m"
    and "Run m t a" and "invariant s" and "reads_regs_from inv_regs t s"
  shows "invariant (the (updates_regs inv_regs t s))"
  using assms
  by (auto elim!: runs_preserve_invariantE)

lemma traces_preserve_invariant_Traces_invariant[simp]:
  assumes "traces_preserve_invariant m"
    and "(m, t, m') \<in> Traces" and "invariant s" and "reads_regs_from inv_regs t s"
  shows "invariant (the (updates_regs inv_regs t s))"
  using assms
  by (auto elim!: traces_preserve_invariantE)

lemma bind_Traces_inv_cases:
  assumes "(m \<bind> f, t, m') \<in> Traces_inv regs" and "runs_preserve_invariant m"
  obtains (Ex) e where "(m, t, Exception e) \<in> Traces_inv regs" and "m' = Exception e"
  | (Fail) msg where "(m, t, Fail msg) \<in> Traces_inv regs" and "m' = Fail msg"
  | (Bind) tm am tf where "t = tm @ tf" and "Run_inv m tm am regs"
      and "(f am, tf, m') \<in> Traces_inv (the (updates_regs inv_regs tm regs))"
  using assms Bind[of t "[]"]
  unfolding in_Traces_inv_iff
  by (auto elim!: bind_Traces_cases final_bind_cases simp: Run_inv_def regstate_simp elim: final_cases)

lemma determ_traces_bindI:
  assumes "determ_traces m" and "runs_preserve_invariant m"
    and "\<And>t a regs. Run_inv m t a regs \<Longrightarrow> determ_traces (f a)"
  shows "determ_traces (m \<bind> f)"
  unfolding determ_traces_def
  using assms
  by (auto simp: Run_inv_iff_Traces_inv elim!: bind_Traces_inv_cases final_bind_cases
           dest!: determ_the_outcome_eq[OF assms(1), rotated] determ_the_outcome_eq[OF assms(3), rotated])

lemma try_catch_eq_iff:
  "(try_catch m h = Done a) \<longleftrightarrow> (m = Done a \<or> (\<exists>e. m = Exception e \<and> h e = Done a))"
  "(try_catch m h = Exception e) \<longleftrightarrow> (\<exists>e'. m = Exception e' \<and> h e' = Exception e)"
  "(try_catch m h = Fail msg) \<longleftrightarrow> (m = Fail msg \<or> (\<exists>e. m = Exception e \<and> h e = Fail msg))"
  by (cases m; auto)+

lemma try_catch_Traces_inv_cases:
  assumes "(try_catch m h, t, mtc) \<in> Traces_inv regs" and "traces_preserve_invariant m"
  obtains (Done) a where "Run_inv m t a regs" and "mtc = Done a"
  | (Fail) msg where "(m, t, Fail msg) \<in> Traces_inv regs" and "mtc = Fail msg"
  | (Ex) tm ex th where "(m, tm, Exception ex) \<in> Traces_inv regs"
      and "(h ex, th, mtc) \<in> Traces_inv (the (updates_regs inv_regs tm regs))" and "t = tm @ th"
  using assms
  unfolding in_Traces_inv_iff Run_inv_def
  by (auto elim!: try_catch_Traces_cases final_cases simp: regstate_simp try_catch_eq_iff; fastforce)

lemma determ_traces_try_catchI:
  assumes "determ_traces m" and "traces_preserve_invariant m"
    and "\<And>e. determ_traces (h e)"
  shows "determ_traces (try_catch m h)"
  unfolding determ_traces_def
  using assms determ_the_outcome_eq[OF assms(3)] determ_the_outcome_eq[OF assms(1)]
  by (fastforce simp: Run_inv_iff_Traces_inv elim!: try_catch_Traces_inv_cases
                dest!: determ_the_outcome_eq[OF assms(1), rotated] determ_the_outcome_eq[OF assms(3), rotated])

lemma determ_traces_liftR[determ]:
  assumes "determ_traces m" and "traces_preserve_invariant m"
  shows "determ_traces (liftR m)"
  using assms
  unfolding liftR_def
  by (auto intro!: determ_traces_try_catchI determ)

lemma determ_traces_catch_early_return[determ]:
  assumes "determ_traces m" and "traces_preserve_invariant m"
  shows "determ_traces (catch_early_return m)"
  using assms
  unfolding catch_early_return_def
  by (auto intro!: determ_traces_try_catchI determ split: sum.splits)

lemma determ_traces_early_return[determ]:
  "determ_traces (early_return a)"
  by (auto simp: early_return_def intro: determ)

lemma determ_traces_foreachM:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> determ_traces (body x vars)"
    and "\<And>x vars. x \<in> set xs \<Longrightarrow> runs_preserve_invariant (body x vars)"
  shows "determ_traces (foreachM xs vars body)"
  using assms
  by (induction xs arbitrary: vars) (auto intro: determ determ_traces_bindI)

lemma determ_runs_if:
  "determ_runs (if c then m1 else m2)" if "c \<Longrightarrow> determ_runs m1" and "\<not>c \<Longrightarrow> determ_runs m2"
  using that
  by auto

lemma determ_traces_if:
  "determ_traces (if c then m1 else m2)" if "c \<Longrightarrow> determ_traces m1" and "\<not>c \<Longrightarrow> determ_traces m2"
  using that
  by auto

lemma determ_traces_read_inv_reg:
  assumes "name r \<in> inv_regs"
    and "\<forall>regs. invariant regs \<longrightarrow> get_regval (name r) regs = Some v \<and> of_regval r v = Some (read_from r regs)"
  shows "determ_traces (read_reg r)"
  using assms
  by (intro determ_tracesI[where m' = "Done (the (of_regval r v))"])
     (auto simp: Traces_inv_def read_reg_def elim!: Read_reg_TracesE final_cases split: option.splits)

lemma determ_runs_read_inv_reg:
  "determ_runs (read_reg r)" if "name r \<in> inv_regs" and "\<And>regs. invariant regs \<Longrightarrow> get_regval (name r) regs = Some v"
  using that
  by (intro determ_runsI[where c = "the (of_regval r v)"])
     (auto simp: determ_runs_def Run_inv_def elim!: Run_read_regE)

lemma determ_runs_or_boolM[determ]:
  "determ_runs (or_boolM m1 m2)" if "determ_runs m1" and "determ_runs m2" and "runs_preserve_invariant m1"
  using that
  unfolding or_boolM_def
  by (auto intro!: determ_runs_bindI determ_runs_return)

lemma determ_runs_assert_exp[determ]: "determ_runs (assert_exp e msg)"
  by (intro determ_runsI) auto

lemma determ_runs_case_prod[determ]:
  "determ_runs (case x of (y, z) \<Rightarrow> f y z)" if "\<And>y z. x = (y, z) \<Longrightarrow> determ_runs (f y z)"
  using that
  by auto

lemma determ_runs_case_option[determ]:
  "determ_runs (case x of Some y \<Rightarrow> f y | None \<Rightarrow> g)" if "\<And>y. x = Some y \<Longrightarrow> determ_runs (f y)" and "determ_runs g"
  using that
  by (cases x) auto

lemma determ_traces_exit[determ]: "determ_traces (exit0 u)"
  by (intro determ_tracesI) (auto simp: exit0_def in_Traces_inv_iff)

lemmas determ_runs_exit0 = determ_traces_exit[THEN determ_traces_runs, determ]

end

end
