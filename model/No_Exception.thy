theory No_Exception

imports
  "Sail.Sail2_state_lemmas"
  "HOL-Eisbach.Eisbach_Tools"
  "Bound_UntilM"

begin

text \<open>
Show that an action in the monad does not result in exceptions.

Comes with a gadget for proving lots of such theorems with little
supervision.
\<close>
definition
  monad_no_exception :: "('e set) \<Rightarrow> ('regv, 'a, 'e) monad \<Rightarrow> bool"
  where
  "monad_no_exception S m = (\<forall>t res. (m, t, res) \<in> Traces \<longrightarrow> (res \<notin> Exception ` (- S)))"

lemmas monad_no_exceptionD = monad_no_exception_def[THEN iffD1, rule_format]

lemma monad_no_exception_weaken:
  "monad_no_exception S f \<Longrightarrow> S \<subseteq> S' \<Longrightarrow>
    monad_no_exception S' f"
  by (auto simp: monad_no_exception_def)

lemma bind_exception_case:
  "(f \<bind> (\<lambda>x. g x), t, Exception e) \<in> Traces \<Longrightarrow>
    (f, t, Exception e) \<in> Traces \<or>
    (\<exists>t' x t''. Run f t' x \<and> (g x, t'', Exception e) \<in> Traces \<and> t = t' @ t'')"
  apply (erule bind_Traces_cases)
   apply (case_tac m''; simp)
   apply auto
  done

lemma monad_no_exception_bind:
  "monad_no_exception S f \<Longrightarrow>
    (\<forall>x t. Run f t x \<longrightarrow> monad_no_exception S' (g x)) \<Longrightarrow>
    monad_no_exception (S \<union> S') (bind f (\<lambda>x. g x))"
  apply (subst monad_no_exception_def, clarsimp)
  apply (drule bind_exception_case)
  apply (auto simp: monad_no_exception_def)
  apply fastforce
  done

lemma monad_no_exception_bind_simple:
  "monad_no_exception S f \<Longrightarrow>
    (\<And>x. monad_no_exception S (g x)) \<Longrightarrow>
    monad_no_exception S (bind f (\<lambda>x. g x))"
  by (drule monad_no_exception_bind, auto)

lemmas monad_no_exception_bind_backward =
  monad_no_exception_bind[where S=S and S'=S for S, simplified]

lemma try_catch_monad_no_exception:
  "monad_no_exception Q f \<Longrightarrow>
    (\<forall>x t. (f, t, Exception x) \<in> Traces \<and> x \<in> Q\<longrightarrow> monad_no_exception S (g x)) \<Longrightarrow>
    monad_no_exception S (try_catch f (\<lambda>x. g x))"
  apply (subst monad_no_exception_def, clarsimp)
  apply (erule try_catch_Traces_cases)
   apply (drule(1) monad_no_exceptionD)
   apply (case_tac m'; clarsimp)
   apply (drule spec, drule mp, rule conjI, erule exI)
    apply blast
   apply (clarsimp dest!: sym[where s="Exception _"])
   apply (simp add: monad_no_exception_def)
  apply (drule spec, drule mp, rule conjI, erule exI)
   apply (drule(1) monad_no_exceptionD)+
   apply auto[1]
  apply (drule(1) monad_no_exceptionD)+
  apply auto
  done

named_theorems monad_no_exception

lemma monad_no_exception_return[monad_no_exception]:
  "monad_no_exception {} (return x)"
  by (clarsimp simp add: monad_no_exception_def return_def)

lemma monad_no_exception_throw[monad_no_exception]:
  "monad_no_exception {x} (throw x)"
  by (clarsimp simp add: monad_no_exception_def throw_def)

definition
  sum_right_restrict :: "'b set \<Rightarrow> ('a + 'b) set"
  where
  "sum_right_restrict S = ((Inr ` S) \<union> range Inl)"

lemma sum_right_restrict_simps[simp]:
  "Inl x \<in> sum_right_restrict S"
  "(Inr x \<in> sum_right_restrict S) = (x \<in> S)"
  by (auto simp add: sum_right_restrict_def)

lemma catch_early_return_no_exception:
  "monad_no_exception (sum_right_restrict S) m \<Longrightarrow>
    monad_no_exception S (catch_early_return m)"
  apply (simp add: catch_early_return_def)
  apply (erule try_catch_monad_no_exception)
  apply (clarsimp split: sum.split)
  apply (intro conjI impI allI
    monad_no_exception_return[THEN monad_no_exception_weaken], simp_all)
  apply (rule monad_no_exception_weaken, rule monad_no_exception_throw)
  apply simp
  done

lemmas monad_no_exception_early_return[monad_no_exception] =
    monad_no_exception_throw[where x="Inl rv" for rv, folded early_return_def]

lemma liftR_no_exception:
  "monad_no_exception S f \<Longrightarrow>
    monad_no_exception (sum_right_restrict S) (liftR f)"
  apply (simp add: liftR_def)
  apply (erule try_catch_monad_no_exception)
  apply (clarsimp)
  apply (rule monad_no_exception_weaken, rule monad_no_exception_throw)
  apply simp
  done

lemma monad_no_exception_Fail[monad_no_exception]:
  "monad_no_exception {} (Fail s)"
  by (clarsimp simp add: monad_no_exception_def)

lemma monad_no_exception_Done[monad_no_exception]:
  "monad_no_exception {} (Done x)"
  by (clarsimp simp add: monad_no_exception_def)

lemma monad_no_exception_maybe_fail[monad_no_exception]:
  "monad_no_exception {} (maybe_fail s x)"
  by (simp add: maybe_fail_def monad_no_exception split: option.split)

lemma read_reg_traces[monad_no_exception]:
  "monad_no_exception {} (read_reg r)"
  apply (clarsimp simp add: monad_no_exception_def read_reg_def)
  apply (erule Traces.cases)
   apply clarsimp
  apply (erule T.cases; clarsimp split: option.split_asm)
  done

lemma write_reg_traces[monad_no_exception]:
  "monad_no_exception {} (write_reg r x)"
  apply (clarsimp simp add: monad_no_exception_def write_reg_def)
  apply (erule Traces.cases)
   apply clarsimp
  apply (erule T.cases; clarsimp split: option.split_asm)
  done

ML \<open>
structure Auto_Split_Tac = struct

fun add_consts i (Const c) xs = ((i, c) :: xs)
  | add_consts i (f $ x) xs = add_consts (i + 1) x (add_consts i f xs)
  | add_consts _ _ xs = xs

fun const_name_to_split thy nm = let
    val x = BNF_LFP_Compat.get_info thy [] (Long_Name.qualifier nm)
  in Option.map (#split) x end

fun tac ctxt = SUBGOAL (fn (t, i) => let
    val concl = Logic.strip_assums_concl t
    val cs = add_consts 0 concl [] |> map (apsnd fst)
        |> sort_distinct (prod_ord int_ord fast_string_ord)
    val thy = Proof_Context.theory_of ctxt
    val split = get_first (const_name_to_split thy) (map snd cs)
  in case split of NONE => no_tac
    | SOME t => Splitter.split_tac ctxt [t] i end)

fun meth ctxt = Method.SIMPLE_METHOD (tac ctxt 1)

end
\<close>

method_setup auto_split = \<open>Scan.succeed () >> K Auto_Split_Tac.meth\<close>

method monad_no_exceptionI uses rules = (determ \<open>
    intro allI conjI impI monad_no_exception_bind_simple
        monad_no_exception empty_subsetI
  | rule rules monad_no_exception
  | (rule monad_no_exception_weaken, rule rules monad_no_exception)
  | auto_split\<close>)+

lemma Read_mem_monad_no_exception:
  "(\<forall>x. monad_no_exception {} (f x)) \<Longrightarrow>
    monad_no_exception {} (Read_mem rk x sz f)"
  apply (clarsimp simp: monad_no_exception_def)
  apply (erule Traces.cases; clarsimp)
  apply (erule T.cases; clarsimp)
  apply fastforce
  done

lemma read_mem_monad_no_exception[monad_no_exception]:
  "monad_no_exception {}
    (read_mem dict_Sail2_values_Bitvector_a dict_Sail2_values_Bitvector_b rk addr_sz addr sz)"
  apply (simp add: read_mem_def read_mem_bytes_def maybe_fail_def[symmetric])
  apply (monad_no_exceptionI rules: Read_mem_monad_no_exception)
  done

lemma Write_mem_monad_no_exception:
  "(\<forall>x. monad_no_exception {} (f x)) \<Longrightarrow>
    monad_no_exception {} (Write_mem wk x sz v f)"
  apply (clarsimp simp: monad_no_exception_def)
  apply (erule Traces.cases; clarsimp)
  apply (erule T.cases; clarsimp)
  apply fastforce
  done

lemma write_mem_monad_no_exception[monad_no_exception]:
  "monad_no_exception {}
    (write_mem class_a class_b wk addr_sz addr sz v)"
  apply (simp add: write_mem_def read_mem_bytes_def maybe_fail_def split: option.split)
  apply (monad_no_exceptionI rules: Write_mem_monad_no_exception)
  done

lemma or_boolM_no_exception:
  "monad_no_exception S m \<Longrightarrow> monad_no_exception S m' \<Longrightarrow>
    monad_no_exception S (or_boolM m m')"
  apply (simp add: or_boolM_def)
  apply (monad_no_exceptionI | simp)+
  done

lemma and_boolM_no_exception:
  "monad_no_exception S m \<Longrightarrow> monad_no_exception S m' \<Longrightarrow>
    monad_no_exception S (and_boolM m m')"
  apply (simp add: and_boolM_def)
  apply (monad_no_exceptionI | simp)+
  done

lemma let_unfold_no_exception:
  "monad_no_exception S (f s) \<Longrightarrow>
    monad_no_exception S (Let s f)"
  by simp

lemma let_simple_no_exception:
  "(\<And>s. monad_no_exception S (f s)) \<Longrightarrow>
    monad_no_exception S (Let s f)"
  by simp

lemma bound_untilM_no_exception:
  "(\<forall>vars. monad_no_exception S (cond vars)) \<Longrightarrow>
    (\<forall>vars. monad_no_exception S (body vars)) \<Longrightarrow>
    monad_no_exception S (bound_untilM bound vars cond body)"
  apply (induct bound vars cond body rule: bound_untilM.induct)
  apply (subst bound_untilM.simps)
  apply (intro monad_no_exception_bind_backward allI impI)
    apply (monad_no_exceptionI | clarsimp)+
  done

lemma foreachM_monad_no_exception:
  "(\<And>x vs tr e. x \<in> set xs \<Longrightarrow> monad_no_exception S (body x vs)) \<Longrightarrow>
   monad_no_exception S (foreachM xs vs body)"
  by (induct xs arbitrary: vs, (monad_no_exceptionI | simp)+)

lemma genlistM_monad_no_exception:
  "(\<And>i. i < n \<Longrightarrow> monad_no_exception S (f i)) \<Longrightarrow> monad_no_exception S (genlistM f n)"
  apply (clarsimp simp add: genlistM_def genlist_def)
  apply (monad_no_exceptionI rules: foreachM_monad_no_exception | simp)+
  done

lemma monad_no_exception_Choose:
  "(\<forall>b. monad_no_exception S (cont b)) \<Longrightarrow>
    monad_no_exception S (Choose nm cont)"
  apply (clarsimp simp: monad_no_exception_def)
  apply (erule Traces.cases; clarsimp)
  apply (auto elim!: T.cases)
  done

named_theorems monad_no_exception_intro

lemmas monad_no_exception_intro_init[monad_no_exception_intro] =
    conjI impI allI Un_least monad_no_exception_bind_simple
    or_boolM_no_exception and_boolM_no_exception
    catch_early_return_no_exception let_simple_no_exception
    liftR_no_exception monad_no_exception_Choose
    foreachM_monad_no_exception genlistM_monad_no_exception
    bound_untilM_no_exception
    if_split[where P="monad_no_exception _", THEN iffD2]
    prod.split[where P="monad_no_exception _", THEN iffD2]
    option.split[where P="monad_no_exception _", THEN iffD2]

lemmas monad_no_exception_Choose_return =
    monad_no_exception_Choose[rule_format, OF monad_no_exception_return, simplified]

ML \<open>
structure Monad_No_Exception_Exploration = struct

val triv = Thm.trivial @{cprop "monad_no_exception S m"}
  |> Drule.generalize (["'a", "'b", "'c"], ["S", "m"])

fun dest_eq2 t = Logic.dest_equals t
  handle TERM _ => HOLogic.dest_eq (HOLogic.dest_Trueprop t)

fun is_monadT (Type (@{type_name monad}, _)) = true
  | is_monadT _ = false

val is_meta_monadT = is_monadT o snd o strip_type

fun is_monad_const t = let
    val (f, xs) = strip_comb t
  in is_Const f andalso is_monadT (fastype_of t)
    andalso not (exists (is_meta_monadT o fastype_of) xs) end

fun add_monad_consts [] xs = xs
  | add_monad_consts ((f $ x) :: ts) xs = add_monad_consts (f :: x :: ts)
    ((if is_monad_const (f $ x) then [f $ x] else []) @ xs)
  | add_monad_consts (Abs (nm, ty, t) :: ts) xs = let
    val t' = betapply (Abs (nm, ty, t), Var ((suffix "_bv" nm, 0), ty))
  in add_monad_consts (t' :: ts) xs end
  | add_monad_consts (_ :: ts) xs = add_monad_consts ts xs

fun fetch_by_term ctxt extras term = let
    val inst = Drule.infer_instantiate ctxt
        [(("m", 0), Thm.cterm_of ctxt term)] triv
    val thms = Named_Theorems.get ctxt @{named_theorems "monad_no_exception"}
    val resn = (extras @ thms) RL [inst]
  in case resn of [] => raise TERM ("fetch_by_term", [term])
    | (t :: _) => t
  end

fun dest (Const (@{const_name monad_no_exception}, _) $ S $ m) = (S, m)
  | dest t = raise TERM ("monad_no_exception dest", [t])

fun get_prop ctxt tm sub_thm_concls = let
    val _ = not (null sub_thm_concls) orelse raise TERM ("get_prop: no sub thms", [tm])
    val S_ty = dest (hd sub_thm_concls) |> fst |> fastype_of
    val S = Const (@{const_name bot}, S_ty)
    val inst = Drule.infer_instantiate ctxt
        [(("m", 0), Thm.cterm_of ctxt tm), (("S", 0), Thm.cterm_of ctxt S)] triv
  in Thm.concl_of inst end

fun prove ctxt extras defn = let
    val freeze_defn = Variable.import_vars ctxt defn
    val prop = Thm.concl_of freeze_defn
    val (term, expanded) = dest_eq2 prop
    val sub_fs = add_monad_consts [expanded] []
        |> sort_distinct Term_Ord.fast_term_ord
    val sub_thms = map (fetch_by_term ctxt extras) sub_fs
    val sub_thm_insts = sub_thms RL @{thms monad_no_exception_weaken}
    val prop = get_prop ctxt term (map (Thm.concl_of #> HOLogic.dest_Trueprop) sub_thms)
    val subset_ss = put_simpset HOL_ss ctxt addsimps @{thms subset_iff mem_simps}
    val intros = Named_Theorems.get ctxt @{named_theorems monad_no_exception_intro}
    val tac = simp_tac (put_simpset HOL_basic_ss ctxt addsimps [defn])
        THEN_ALL_NEW REPEAT_ALL_NEW (match_tac ctxt
            (intros @ sub_thm_insts))
        THEN_ALL_NEW simp_tac subset_ss
        THEN_ALL_NEW simp_tac ctxt
    val nms = Term.add_frees prop [] |> map fst
    fun tr ctxt = Syntax.pretty_term ctxt term
      |> (fn p => Pretty.block [Pretty.str "proving monad_no_exception for: ", p])
      |> Pretty.writeln
  in Goal.prove ctxt nms [] prop (fn r => (tr (#context r); tac 1))
  end

fun defn_name defn = Term.term_name (head_of (fst (dest_eq2 (Thm.concl_of defn))))

fun prove_rec thys ctxt extras nm defn = let
    val thm = prove ctxt extras defn
  in thm :: extras end
  handle TERM ("fetch_by_term", [tm]) => let
      val f = head_of tm
      val _ = is_Const f orelse raise TERM ("prove_rec: stuck", [tm])
      val f_nm = fst (dest_Const f)
      val q = Long_Name.qualifier f_nm
      val _ = member (op =) thys q orelse raise TERM ("prove_rec: not in thys", [tm])
      val def2 = Proof_Context.get_thm ctxt (suffix "_def" f_nm)
      val _ = tracing ("recursing " ^ nm ^ " --> "  ^ f_nm)
      val extras2 = prove_rec thys ctxt extras f_nm def2
    in prove_rec thys ctxt extras2 nm defn end

fun install_rec thys defn thy = let
    val ctxt = Proof_Context.init_global thy
    val thms = prove_rec thys ctxt [] "toplevel" defn
  in Context.theory_map
    (fold (Named_Theorems.add_thm @{named_theorems "monad_no_exception"}) thms)
    thy
  end

fun install_recs thys = fold (install_rec thys)

end
\<close>

lemma choose_bool_monad_no_exception[monad_no_exception]:
  "monad_no_exception {} (choose_bool dict s)"
  by (simp add: choose_bool_def choose_convert_def
    monad_no_exception_Choose monad_no_exception_maybe_fail)

lemma bool_of_bitU_nondet_monad_no_exception[monad_no_exception]:
  "monad_no_exception {} (bool_of_bitU_nondet dict bitU)"
  by (cases bitU, simp_all add: bool_of_bitU_nondet_def, monad_no_exceptionI)

setup \<open>Monad_No_Exception_Exploration.install_recs
  ["Sail2_prompt_monad", "Sail2_prompt"]
  @{thms exit0_def assert_exp_def of_bits_nondet_def}\<close>

end
