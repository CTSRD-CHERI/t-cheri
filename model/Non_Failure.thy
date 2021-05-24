theory Non_Failure

imports
  "Trace_Assumptions"

begin

lemma final_helper:
  "\<forall>x. P x \<Longrightarrow> f = g \<Longrightarrow> \<forall>x. P x \<longrightarrow> f x = g x"
  by simp

lemma nchotomy_helper:
  "(\<exists>x y. P x y) = (\<exists>t. P (fst t) (snd t))"
  "(\<forall>x. (\<exists>y. x = f y) \<longrightarrow> Q x) = (\<forall>y. Q (f y))"
  by auto

lemmas final_simps2[simp] = final_helper[OF monad.nchotomy final_def,
    simplified imp_disjL all_conj_distrib, simplified nchotomy_helper,
    simplified]

lemma final_bind_eq:
  "final (f \<bind> g) = (final f \<and> (case f of Done x \<Rightarrow> final (g x) | _ \<Rightarrow> True))"
  by (cases f, simp_all add: final_def)

lemma final_bind_TraceD:
  "(f \<bind> g, tr, x) \<in> Traces \<Longrightarrow> final x \<Longrightarrow>
    (\<exists>y tr_a tr_b. (f, tr_a, y) \<in> Traces \<and> final y \<and> tr = tr_a @ tr_b \<and>
        (case y of Done v \<Rightarrow> (g v, tr_b, x) \<in> Traces \<and> final x
            | _ \<Rightarrow> tr_b = [] \<and> (\<exists>rv. x = monad.map_monad (\<lambda>_. rv) id y)))"
proof (induct m \<equiv> "f \<bind> g" tr x arbitrary: f g rule: Traces.induct)
  case Nil
  then show ?case
   apply (clarsimp simp: final_bind_eq)
   apply (intro exI conjI, rule Traces.Nil)
    apply simp
   apply (clarsimp split: monad.split_asm simp: Traces.Nil)
   done
next
  case (Step e s'' t s')
  show ?case using Step.hyps(1-2) Step.prems
    apply (safe elim!: bind_T_cases)
     apply (clarsimp simp: final_def[THEN fun_cong, where x="Done _"])
     apply (erule(1) Traces.Step)
    apply (drule(1) Step, clarsimp)
    apply (intro exI conjI, erule(1) Traces.Step)
      apply simp
     apply simp
    apply (clarsimp split: monad.split_asm)
    done
qed

definition
  exec_success_inner :: "bool \<Rightarrow> ('r, 'a, 'e) monad \<Rightarrow> 'r event list \<Rightarrow> bool"
  where
  "exec_success_inner exceptions f tr = (\<forall>x. (f, tr, x) \<in> Traces \<longrightarrow> final x \<longrightarrow>
    (case x of Done _ \<Rightarrow> True | Exception _ \<Rightarrow> exceptions | _ \<Rightarrow> False))"

lemmas exec_success_innerD = exec_success_inner_def[THEN iffD1, rule_format]

lemma exec_success_inner_exc_imp:
  "exec_success_inner exc f tr \<Longrightarrow> exc \<longrightarrow> exc2 \<Longrightarrow>
    exec_success_inner exc2 f tr"
  apply (clarsimp simp: exec_success_inner_def)
  apply (drule spec, drule(1) mp)
  apply (clarsimp split: monad.split_asm)
  done

definition
  exec_success :: "('r, 'a, 'e) monad \<Rightarrow> ('r event list \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "exec_success f assum pre = (\<forall>tr. pre \<and> assum tr \<longrightarrow> exec_success_inner False f tr)"

lemmas exec_successI = exec_success_def[THEN iffD2, rule_format]

definition
  "is_precondition f = True"

lemma exec_success_imp:
  "exec_success f assum pre \<Longrightarrow>
    (is_precondition f \<Longrightarrow> pre \<and> assum tr) \<Longrightarrow>
    exec_success_inner exc f tr"
  by (clarsimp simp: is_precondition_def exec_success_def
        exec_success_inner_exc_imp[where exc=False])

lemma exec_success_inner_bind:
  assumes f: "\<And>tr_a tr_b. tr = tr_a @ tr_b \<Longrightarrow> exec_success_inner exc f tr_a"
  and g: "\<And>tr_a tr_b v. tr = tr_a @ tr_b \<Longrightarrow> Run f tr_a v \<Longrightarrow> exec_success_inner exc (g v) tr_b"
  shows "exec_success_inner exc (f \<bind> g) tr"
  apply (clarsimp simp: exec_success_inner_def)
  apply (drule(1) final_bind_TraceD, clarsimp)
  apply (frule f, drule(2) exec_success_innerD)
  apply (clarsimp split: monad.split_asm)
  apply (frule(1) g)
  apply (simp add: exec_success_inner_def)
  done

lemma exec_success_inner_Choose:
  "(\<forall>v tr_b. tr = E_choose nm v # tr_b \<longrightarrow> exec_success_inner exc (f v) tr_b) \<Longrightarrow>
    exec_success_inner exc (Choose nm f) tr"
  apply (clarsimp simp: exec_success_inner_def)
  apply (erule Traces_cases, simp_all)
  apply clarsimp
  done

lemmas exec_success_inner_inst_simps[simp] =
    exec_success_inner_def[where f="return _", simplified]
    exec_success_inner_def[where f="Done _", simplified]
    exec_success_inner_def[where f="throw _", simplified]
    exec_success_inner_def[where f="Exception _", simplified]

named_theorems exec_success

lemma assert_exp_exec_success[exec_success]:
  "exec_success (assert_exp P nm) (\<lambda>_. True) P"
  by (rule exec_successI, simp add: assert_exp_def)

definition
  regs_ok :: "(string \<times> (('a \<Rightarrow> bool) \<times> 'b)) list \<Rightarrow> 'a event list \<Rightarrow> bool"
  where
  "regs_ok regs tr = (\<forall>ev \<in> set tr. register_reads_ok (map_option fst o Map.map_of regs) ev)"

lemma regs_ok_append[simp]:
  "regs_ok regs (xs @ ys) = (regs_ok regs xs \<and> regs_ok regs ys)"
  by (auto simp add: regs_ok_def)

lemma read_reg_success:
  "exec_success (read_reg r) (regs_ok regs)
    (map_of regs (name r) = Some (register_ops_of r))"
  apply (clarsimp simp: exec_success_inner_def intro!: exec_successI)
  apply (frule read_reg_non_failure[where f="map_option fst o map_of regs"], simp+)
   apply (simp add: regs_ok_def)
  apply auto
  done

term "\<forall>c. c \<in> C \<longrightarrow> c \<in> derivable C"

lemma write_reg_success[exec_success]:
  "exec_success (write_reg r v) (\<lambda>_. True) True"
  apply (clarsimp simp: exec_success_inner_def intro!: exec_successI)
  apply (simp add: write_reg_def)
  apply (erule Traces.cases)
   apply (clarsimp simp: final_def[THEN fun_cong, where x="Write_reg _ _ _"])
  apply (erule T.cases; clarsimp)
  done

definition
  regs_known :: "(string \<times> (('a \<Rightarrow> bool) \<times> 'b)) list \<Rightarrow> 'a event list \<Rightarrow> bool"

lemma exec_success_inner_foreachM:
  "(\<forall>x y tr'. x \<in> set xs \<longrightarrow> exec_success_inner exc (f x y) tr') \<Longrightarrow>
    exec_success_inner exc (foreachM xs y f) tr"
  apply (induct xs arbitrary: y tr)
   apply simp
  apply simp
  apply (rule exec_success_inner_bind)
   apply simp
  apply simp
  done

lemmas monad_unfolds = and_boolM_def or_boolM_def Let_def[THEN meta_eq_to_obj_eq]

lemmas exec_success_inner_unfold =
    monad_unfolds[THEN ssubst[where P="\<lambda>m. exec_success_inner _ m _ "]]

definition
  unat_range_less :: "('a :: len) word \<Rightarrow> nat \<Rightarrow> bool"
  where
  "unat_range_less w n = (unat w < n)"

lemma unat_range_0[simp]:
  "\<not> unat_range_less w 0"
  by (simp add: unat_range_less_def)

lemma unat_range_step[simp]:
  "n > 0 \<Longrightarrow> w \<noteq> of_nat (n - 1) \<Longrightarrow> unat_range_less w n = unat_range_less w (n - 1)"
  apply (clarsimp simp: unat_range_less_def)
  apply (cases "unat w = n - 1", simp_all)
   apply (cut_tac x=w in unat_lt2p, simp)
   apply (rule ccontr, erule notE, rule word_unat.Rep_eqD)
   apply (simp add: unat_of_nat)
  apply auto
  done

lemma to_unat_rangeD[unfolded word_size]:
  "x \<noteq> of_nat ((2 ^ size x) - 1) \<Longrightarrow> unat_range_less x (2 ^ size x - 1)"
  apply (drule unat_range_step[rotated])
   apply simp
  apply (simp add: unat_range_less_def)
  done

ML \<open>
fun unat_range_intro_tac ctxt = SUBGOAL (fn (t, i) => let
    val ineqs = Logic.strip_assums_hyp t
      |> map_filter (try (HOLogic.dest_eq o HOLogic.dest_not o HOLogic.dest_Trueprop))
      |> filter (can (HOLogic.dest_number o snd))
    val ineq_tab = Termtab.make_list ineqs
    val thms = Termtab.dest ineq_tab
      |> filter (fn (_, xs) => length xs > 2)
      |> map (fn (t, _) => Var (("z", 0), fastype_of t))
      |> sort_distinct Term_Ord.fast_term_ord
      |> map_filter (try (fn x => Drule.infer_instantiate ctxt
          [(("x", 0), Thm.cterm_of ctxt x)] @{thm to_unat_rangeD}))
      |> map (Simplifier.full_simplify ctxt)
   in dresolve_tac ctxt thms i end)
\<close>

method_setup unat_range_intro = \<open>Scan.succeed (fn ctxt =>
    Method.SIMPLE_METHOD (unat_range_intro_tac ctxt 1))\<close>

lemma
  "(x :: 3 word) \<noteq> 5 \<Longrightarrow> x \<noteq> 6 \<Longrightarrow> x \<noteq> 7 \<Longrightarrow> x \<noteq> 4 \<Longrightarrow> x \<noteq> 3 \<Longrightarrow> x \<noteq> 2 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> x \<noteq> 1 \<Longrightarrow> False"
  by (unat_range_intro, simp)

named_theorems exec_success_intro

lemmas exec_success_if[exec_success_intro] =
    if_split[where P="\<lambda>m. exec_success_inner _ m _", THEN iffD2]

method exec_success_step uses flip = determ \<open>
      clarsimp intro!: exec_successI exec_success_inner_unfold
        split del: if_split simp flip: flip
    | rule conjI exec_success_inner_bind exec_success_intro
    | (rule exec_success_imp, rule exec_success)
    | unat_range_intro
  \<close>

method exec_success uses flip = repeat_new \<open>exec_success_step flip: flip\<close>

lemma success_choose_default[exec_success]:
  "exec_success (choose_convert_default of_rv x nm) (\<lambda>_. True) (True)"
  by (clarsimp simp: choose_convert_default_def
    intro!: exec_successI exec_success_inner_Choose)

lemma success_choose_bool[exec_success]:
  "exec_success (choose_bool dict nm) (\<lambda>_. True) (True)"
  by (simp add: choose_bool_def, exec_success)

lemma success_choose_int[exec_success]:
  "exec_success (choose_int dict nm) (\<lambda>_. True) (True)"
  by (simp add: choose_int_def, exec_success)

lemma exec_success_bool_of_bitU_nondet[exec_success]:
  "exec_success (bool_of_bitU_nondet dict b) (\<lambda>_. True) True"
  by (simp add: bool_of_bitU_nondet_def split: bitU.split, exec_success)

lemma exec_success_of_bits_nondet[exec_success]:
  "exec_success (bools_of_bits_nondet dict bits) (\<lambda>_. True) True"
  apply (simp add: bools_of_bits_nondet_def)
  apply (exec_success | rule exec_success_inner_foreachM)+
  done

lemma exec_success_bools_of_bits_nondet[exec_success]:
  "exec_success (of_bits_nondet dict_a dict_b bits) (\<lambda>_. True) True"
  by (simp add: of_bits_nondet_def, exec_success)

lemma success_choose_from_list[exec_success]:
  "exec_success (choose_from_list dict nm xs) (\<lambda>_. True) (xs \<noteq> [])"
  by (simp add: choose_from_list_def, exec_success)

end