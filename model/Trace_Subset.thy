theory Trace_Subset

imports
  "Sail.Sail2_state_lemmas"
  "HOL-Eisbach.Eisbach_Tools"
  "Bound_UntilM"

begin

text \<open>
Show that an action in the monad can only create trace events
within some set. This tends to be a coarse overapproximation,
with no contextual dependency information, but it is useful for
quickly showing that an action depends on some registers and not
others, for instance.

Comes with a gadget for proving lots of such theorems with little
supervision.
\<close>
definition
  monad_trace_subset :: "'regv event set \<Rightarrow> ('regv, 'a, 'e) monad \<Rightarrow> bool"
  where
  "monad_trace_subset S m = (\<forall>t res. (m, t, res) \<in> Traces \<longrightarrow> set t \<subseteq> S)"

lemmas monad_trace_subsetD = monad_trace_subset_def[THEN iffD1, rule_format]

lemma monad_trace_subset_weaken:
  "monad_trace_subset S f \<Longrightarrow> S \<subseteq> S' \<Longrightarrow>
    monad_trace_subset S' f"
  by (auto simp: monad_trace_subset_def)

lemma monad_trace_subset_bind:
  "monad_trace_subset S f \<Longrightarrow>
    (\<forall>x t. Run f t x \<longrightarrow> monad_trace_subset S' (g x)) \<Longrightarrow>
    monad_trace_subset (S \<union> S') (bind f (\<lambda>x. g x))"
  apply (subst monad_trace_subset_def, clarsimp)
  apply (erule bind_Traces_cases)
   apply (drule(1) monad_trace_subsetD)
   apply blast
  apply (drule spec, drule mp, erule exI)
  apply (drule(1) monad_trace_subsetD)+
  apply auto
  done

lemma monad_trace_subset_bind_simple:
  "monad_trace_subset S f \<Longrightarrow>
    (\<And>x. monad_trace_subset S (g x)) \<Longrightarrow>
    monad_trace_subset S (bind f (\<lambda>x. g x))"
  by (drule monad_trace_subset_bind, auto)

lemmas monad_trace_subset_bind_backward =
  monad_trace_subset_bind[where S=S and S'=S for S, simplified]

lemma try_catch_monad_trace_subset:
  "monad_trace_subset S f \<Longrightarrow>
    (\<forall>x t. (f, t, Exception x) \<in> Traces \<longrightarrow> monad_trace_subset S (g x)) \<Longrightarrow>
    monad_trace_subset S (try_catch f (\<lambda>x. g x))"
  apply (subst monad_trace_subset_def, clarsimp)
  apply (erule try_catch_Traces_cases)
   apply (drule(1) monad_trace_subsetD)
   apply blast
  apply (drule spec, drule mp, erule exI)
  apply (drule(1) monad_trace_subsetD)+
  apply auto
  done

named_theorems monad_trace_subset

lemma monad_trace_subset_return[monad_trace_subset]:
  "monad_trace_subset {} (return x)"
  by (simp add: monad_trace_subset_def return_def)

lemma monad_trace_subset_throw[monad_trace_subset]:
  "monad_trace_subset {} (throw x)"
  by (simp add: monad_trace_subset_def throw_def)

lemma monad_trace_subset_Fail[monad_trace_subset]:
  "monad_trace_subset {} (Fail s)"
  by (simp add: monad_trace_subset_def)

lemma monad_trace_subset_Done[monad_trace_subset]:
  "monad_trace_subset {} (Done x)"
  by (simp add: monad_trace_subset_def)

lemma monad_trace_subset_maybe_fail[monad_trace_subset]:
  "monad_trace_subset {} (maybe_fail s x)"
  by (simp add: maybe_fail_def monad_trace_subset split: option.split)

lemma read_reg_traces[monad_trace_subset]:
  "monad_trace_subset (range (E_read_reg (name r))) (read_reg r)"
  apply (clarsimp simp add: monad_trace_subset_def read_reg_def)
  apply (erule Traces.cases)
   apply simp
  apply clarsimp
  apply (erule T.cases; clarsimp split: option.split_asm)
  done

lemma write_reg_traces[monad_trace_subset]:
  "monad_trace_subset (range (E_write_reg (name r))) (write_reg r x)"
  apply (clarsimp simp add: monad_trace_subset_def write_reg_def)
  apply (erule Traces.cases)
   apply simp
  apply clarsimp
  apply (erule T.cases; clarsimp split: option.split_asm)
  done

method monad_trace_subsetI uses rules = (determ \<open>
    intro allI conjI impI monad_trace_subset_bind_simple
        monad_trace_subset empty_subsetI
  | rule rules monad_trace_subset
  | (rule monad_trace_subset_weaken, rule rules monad_trace_subset)\<close>)+

lemma Read_mem_monad_trace_subset:
  "(\<forall>x. monad_trace_subset {} (f x)) \<Longrightarrow>
    monad_trace_subset (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val))
        (Read_mem rk x sz f)"
  apply (clarsimp simp: monad_trace_subset_def)
  apply (erule Traces.cases; clarsimp)
  apply (erule T.cases; clarsimp)
  apply fastforce
  done

lemma read_mem_monad_trace_subset[monad_trace_subset]:
  "monad_trace_subset (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val))
    (read_mem dict_Sail2_values_Bitvector_a dict_Sail2_values_Bitvector_b rk addr_sz addr sz)"
  apply (simp add: read_mem_def read_mem_bytes_def maybe_fail_def[symmetric])
  apply (monad_trace_subsetI rules: Read_mem_monad_trace_subset)
  done

lemma Write_mem_monad_trace_subset:
  "(\<forall>x. monad_trace_subset {} (f x)) \<Longrightarrow>
    monad_trace_subset (range (\<lambda>(wk, addr, val, sz, k). E_write_mem wk addr sz val k))
        (Write_mem wk x sz v f)"
  apply (clarsimp simp: monad_trace_subset_def)
  apply (erule Traces.cases; clarsimp)
  apply (erule T.cases; clarsimp)
  apply fastforce
  done
lemma write_mem_monad_trace_subset[monad_trace_subset]:
  "monad_trace_subset (range (\<lambda>(wk, addr, val, sz, k). E_write_mem wk addr sz val k))
    (write_mem class_a class_b wk addr_sz addr sz v)"
  apply (simp add: write_mem_def read_mem_bytes_def maybe_fail_def split: option.split)
  apply (monad_trace_subsetI rules: Write_mem_monad_trace_subset)
  done

lemma catch_early_return_trace_subset:
  "monad_trace_subset S m \<Longrightarrow>
    monad_trace_subset S (catch_early_return m)"
  apply (simp add: catch_early_return_def)
  apply (rule try_catch_monad_trace_subset; clarsimp split: sum.split)
  apply monad_trace_subsetI
  done

lemma or_boolM_trace_subset:
  "monad_trace_subset S m \<Longrightarrow> monad_trace_subset S m' \<Longrightarrow>
    monad_trace_subset S (or_boolM m m')"
  apply (simp add: or_boolM_def)
  apply (monad_trace_subsetI | simp)+
  done

lemma and_boolM_trace_subset:
  "monad_trace_subset S m \<Longrightarrow> monad_trace_subset S m' \<Longrightarrow>
    monad_trace_subset S (and_boolM m m')"
  apply (simp add: and_boolM_def)
  apply (monad_trace_subsetI | simp)+
  done

lemma let_trace_subset:
  "monad_trace_subset S (f s) \<Longrightarrow>
    monad_trace_subset S (Let s f)"
  by simp

lemma bound_untilM_trace_subset:
  "(\<forall>vars. monad_trace_subset S (cond vars)) \<Longrightarrow>
    (\<forall>vars. monad_trace_subset S (body vars)) \<Longrightarrow>
    monad_trace_subset S (bound_untilM bound vars cond body)"
  apply (induct bound vars cond body rule: bound_untilM.induct)
  apply (subst bound_untilM.simps)
  apply (intro monad_trace_subset_bind_backward allI impI)
    apply (monad_trace_subsetI | clarsimp)+
  done

lemma liftR_trace_subset:
  "monad_trace_subset S f \<Longrightarrow>
    monad_trace_subset S (liftR f)"
  apply (simp add: liftR_def)
  apply (intro try_catch_monad_trace_subset,
        (monad_trace_subsetI | simp)+)
  done

lemma foreachM_monad_trace_subset:
  "(\<And>x vs tr e. x \<in> set xs \<Longrightarrow> monad_trace_subset S (body x vs)) \<Longrightarrow>
   monad_trace_subset S (foreachM xs vs body)"
  by (induct xs arbitrary: vs, (monad_trace_subsetI | simp)+)

lemma genlistM_monad_trace_subset:
  "(\<And>i. i < n \<Longrightarrow> monad_trace_subset S (f i)) \<Longrightarrow> monad_trace_subset S (genlistM f n)"
  apply (clarsimp simp add: genlistM_def genlist_def)
  apply (monad_trace_subsetI rules: foreachM_monad_trace_subset | simp)+
  done

lemma monad_trace_subset_Choose:
  "(\<forall>b. monad_trace_subset S (cont b)) \<Longrightarrow>
    monad_trace_subset (range (E_choose nm) \<union> S) (Choose nm cont)"
  apply (clarsimp simp: monad_trace_subset_def)
  apply (erule Traces.cases; clarsimp)
  apply (auto elim!: T.cases)
  done

named_theorems monad_trace_subset_intro

lemmas monad_trace_subset_intro_init[monad_trace_subset_intro] =
    conjI impI allI Un_least monad_trace_subset_bind_simple
    or_boolM_trace_subset and_boolM_trace_subset
    catch_early_return_trace_subset let_trace_subset
    liftR_trace_subset monad_trace_subset_Choose
    foreachM_monad_trace_subset genlistM_monad_trace_subset
    bound_untilM_trace_subset
    if_split[where P="monad_trace_subset _", THEN iffD2]
    prod.split[where P="monad_trace_subset _", THEN iffD2]
    option.split[where P="monad_trace_subset _", THEN iffD2]
    bitU.split[where P="monad_trace_subset _", THEN iffD2]

lemmas monad_trace_subset_Choose_return =
    monad_trace_subset_Choose[rule_format, OF monad_trace_subset_return, simplified]

ML \<open>
structure Monad_Trace_Subset_Exploration = struct

val triv = Thm.trivial @{cprop "monad_trace_subset S m"}
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
    val thms = Named_Theorems.get ctxt @{named_theorems "monad_trace_subset"}
    val resn = (extras @ thms) RL [inst]
  in case resn of [] => raise TERM ("fetch_by_term", [term])
    | (t :: _) => t
  end

fun dest (Const (@{const_name monad_trace_subset}, _) $ S $ m) = (S, m)
  | dest t = raise TERM ("monad_trace_subset dest", [t])

fun strip_un (Const (@{const_name "Lattices.sup"}, _) $ x $ y) = maps strip_un [x, y]
  | strip_un t = [t]

fun mk_un [] = raise TERM ("monad_trace_subset mk_un: empty", [])
  | mk_un (x :: xs) = let
    val ty = fastype_of x
    val c = Const (@{const_name "Lattices.sup"}, ty --> ty --> ty)
  in foldr1 (fn (x, y) => c $ x $ y) (x :: xs) end

fun prove ctxt extras defn = let
    val freeze_defn = Variable.import_vars ctxt defn
    val prop = Thm.concl_of freeze_defn
    val (term, expanded) = dest_eq2 prop
    val sub_fs = add_monad_consts [expanded] []
        |> sort_distinct Term_Ord.fast_term_ord
    val sub_thms = map (fetch_by_term ctxt extras) sub_fs
    val ss = map (Thm.concl_of #> HOLogic.dest_Trueprop #> dest #> fst) sub_thms
        |> maps strip_un
        |> sort_distinct Term_Ord.fast_term_ord
    val ss_frees = fold Term.add_vars ss []
    val _ = null ss_frees orelse raise TERM ("monad_trace_subset prove", ss)
    val _ = not (null ss) orelse raise THM ("monad_trace_subset prove: subthms", 1, sub_thms)
    val st = mk_un ss
    val sub_thm_insts = sub_thms RL @{thms monad_trace_subset_weaken}
    val inst = Drule.infer_instantiate ctxt
        [(("m", 0), Thm.cterm_of ctxt term), (("S", 0), Thm.cterm_of ctxt st)] triv
    val subset_ss = put_simpset HOL_ss ctxt addsimps @{thms subset_iff mem_simps}
    val intros = Named_Theorems.get ctxt @{named_theorems monad_trace_subset_intro}
    val tac = simp_tac (put_simpset HOL_basic_ss ctxt addsimps [defn])
        THEN_ALL_NEW REPEAT_ALL_NEW (match_tac ctxt
            (intros @ sub_thm_insts))
        THEN_ALL_NEW simp_tac subset_ss
        THEN_ALL_NEW simp_tac ctxt
    val nms = Term.add_frees (Thm.concl_of inst) [] |> map fst
    fun tr ctxt = Syntax.pretty_term ctxt term
      |> (fn p => Pretty.block [Pretty.str "proving monad_trace_subset for: ", p])
      |> Pretty.writeln
  in Goal.prove ctxt nms [] (Thm.concl_of inst) (fn r => (tr (#context r); tac 1))
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
    (fold (Named_Theorems.add_thm @{named_theorems "monad_trace_subset"}) thms)
    thy
  end

fun install_recs thys = fold (install_rec thys)

end
\<close>

lemma choose_bool_monad_trace_subset[monad_trace_subset]:
  "monad_trace_subset (range (E_choose s)) (choose_bool s)"
  apply (simp add: choose_bool_def)
  apply (rule monad_trace_subset_Choose_return)
  done

lemma bool_of_bitU_nondet_monad_trace_subset[monad_trace_subset]:
  "monad_trace_subset (range (E_choose ''bool_of_bitU'')) (bool_of_bitU_nondet bitU)"
  by (cases bitU, simp_all add: bool_of_bitU_nondet_def, monad_trace_subsetI)

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Sail2_prompt_monad", "Sail2_prompt"]
  @{thms early_return_def exit0_def assert_exp_def
    undefined_bool_def internal_pick_def
    of_bits_nondet_def}
\<close>

end
