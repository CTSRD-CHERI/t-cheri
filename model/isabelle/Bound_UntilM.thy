theory Bound_UntilM

imports
  "Sail.Sail2_prompt"

begin

text \<open>
Adjustment of untilM to add a metric function which guarantees
termination.
\<close>

function
  bound_untilM :: "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> ('b, bool, 'c) monad) \<Rightarrow> ('a \<Rightarrow> ('b, 'a, 'c) monad) \<Rightarrow> ('b, 'a, 'c) monad"
  where
  "bound_untilM bound orig_vars cond body = (
  body orig_vars \<bind> (\<lambda> vars.
  cond vars \<bind> (\<lambda> cond_val.
  if cond_val then return vars
  else if bound vars < bound orig_vars
  then bound_untilM bound vars cond body
    else Fail ''untilM'')))" 
  by pat_completeness auto

termination bound_untilM
  apply (relation "measure (\<lambda>(bound, vs, _, _). bound vs)")
   apply simp
  apply simp
  done

declare bound_untilM.simps[simp del]

lemma coerce_inv_bound_untilM_induct:
  assumes I: "I vs"
  and step: "\<forall>vs vs' t t'. I vs \<and> Run (body vs) t vs' \<and> Run (cond vs') t' False \<longrightarrow>
        I vs' \<and> bound vs' < bound vs"
  shows "untilM_dom (vs, cond, body) \<and> untilM vs cond body = bound_untilM bound vs cond body"
  (is "?dom vs \<and> ?eq vs")
  using I
proof (induct vs rule: measure_induct[where f=bound])
case (1 vs)

  note step2 = step[simplified imp_conjL, rule_format, OF "1.prems"]

  from 1 have dom: "?dom vs"
    by (fastforce intro: accpI elim!: untilM_rel.cases dest!: step2)

  from 1 have eq: "?eq vs"
    apply (subst bound_untilM.simps)
    apply (simp add: untilM.psimps[OF dom])
    apply (intro bind_cong refl if_cong)
    apply (auto dest!: step2)
    done

  from dom eq show ?case by simp
qed

lemmas coerce_inv_bound_untilM =
    coerce_inv_bound_untilM_induct[THEN conjunct2]



end
