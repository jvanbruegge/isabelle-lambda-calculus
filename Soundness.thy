theory Soundness
  imports Defs
begin

theorem progress: "[] \<turnstile> e : \<tau> \<Longrightarrow> is_v_of_e e \<or> (\<exists>e'. Step e e')"
proof (induction "[] :: \<Gamma>" e \<tau> rule: T.induct)
  case T_UnitI
  then show ?case by simp
next
  case (T_VarI x \<tau>)
  then show ?case by simp
next
  case (T_AbsI x \<tau>1 e \<tau>2)
  then show ?case by simp
next
  case (T_AppI e1 \<tau>1 \<tau>2 e2)
  note IH1 = T_AppI(2)
  note IH2 = T_AppI(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_v_of_e e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_v_of_e e2"
      from \<open>is_v_of_e e1\<close> T_AppI have "\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)"
        by (metis T.cases \<tau>.distinct(1) \<tau>.inject is_v_of_e.simps(1) is_v_of_e.simps(3))
      then have "\<exists>e'. Step (App e1 e2) e'" using \<open>is_v_of_e e2\<close> ST_BetaI by blast
      then show ?thesis by simp
    next
      assume "\<exists>e2'. Step e2 e2'"
      then show ?thesis using ST_App2I \<open>is_v_of_e e1\<close> by blast
    qed
  next
    assume "\<exists>e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
qed

definition closed :: "e \<Rightarrow> bool" where
  "closed x \<equiv> fve_e x = []"

lemma list_minus_set: "set (list_minus e xs) = set e - set xs"
  by (induction e) (auto)

lemma free_in_context: "\<lbrakk> x \<in> set (fve_e e) ; \<Gamma> \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> \<exists>\<tau>'. (x, \<tau>') \<in> \<Gamma>"
proof (induction e arbitrary: \<Gamma> \<tau> x)
  case (Var y)
  then show ?case using T.cases by fastforce
next
  case (Lam y \<tau>' e)
  then have "x \<noteq> y" by (simp add: list_minus_set)
  then have "x \<in> set (fve_e e)" using list_minus_set T.cases Lam by fastforce
  then show ?case
    by (metis (no_types, lifting) Lam(3) Lam.IH T.cases \<open>x \<noteq> y\<close> e.distinct(1) e.distinct(9) e.simps(11) e.simps(2) isin.simps(2))
next
  case (App e1 e2)
  then show ?case
    by (metis (no_types, lifting) T.cases UnE e.distinct(11) e.distinct(3) e.distinct(7) e.inject(3) fve_e.simps(3) set_append)
next
  case Unit
  then show ?case by simp
qed

corollary typeable_closed: "[] \<turnstile> e : \<tau> \<Longrightarrow> closed e"
  unfolding closed_def
  using free_in_context last_in_set by fastforce

lemma context_invariance: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; \<forall>x \<tau>'. x \<in> set (fve_e e) \<and> (x, \<tau>') \<in> \<Gamma> \<longrightarrow> (x, \<tau>')\<in>\<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> e : \<tau>"
proof (induction \<Gamma> e \<tau> arbitrary: \<Gamma>' rule: T.induct)
  case (T_UnitI \<Gamma>)
  then show ?case by (simp add: T.T_UnitI)
next
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case by (auto simp: T.T_VarI)
next
  case (T_AbsI y \<tau>1 \<Gamma> e \<tau>2)
  then show ?case by (simp add: T.T_AbsI list_minus_set)
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case by auto (metis (mono_tags, lifting) T.T_AppI)
qed

lemma substitution: "\<lbrakk> (x, \<tau>')#\<Gamma> \<turnstile> e : \<tau> ; [] \<turnstile> v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> esubst_e v x e : \<tau>"
proof (induction "(x, \<tau>')#\<Gamma>" e \<tau> arbitrary: v x \<tau>' \<Gamma> rule: T.induct)
case T_UnitI
  then show ?case by (simp add: T.T_UnitI)
next
  case (T_VarI y \<sigma>)
  then have t: "(x, \<tau>')#\<Gamma> \<turnstile> Var y : \<sigma>" using T.T_VarI by simp
  then show ?case
  proof (cases "y = x")
    case True
    then have "\<sigma> = \<tau>'" using T_VarI by fastforce
    then show ?thesis using T_VarI.prems True context_invariance by fastforce
  next
    case False
    then have "\<Gamma> \<turnstile> Var y : \<sigma>" using t T.T_VarI T_VarI.hyps by auto
    then show ?thesis using False by simp
  qed
next
  case (T_AbsI y \<tau>1 e \<tau>2)
  let ?lam = "(\<lambda> y : \<tau>1 . e)"
  from T_AbsI show ?case
  proof (cases "x = y")
    case True
    then have same: "esubst_e v x ?lam = ?lam" using T_AbsI by simp
    then have fv: "x \<notin> set (fve_e ?lam)" by (simp add: list_minus_set True)
    then have "(x, \<tau>')#\<Gamma> \<turnstile> ?lam : \<tau>1 \<rightarrow> \<tau>2" using T.T_AbsI T_AbsI by simp
    then have "\<Gamma> \<turnstile> ?lam : \<tau>1 \<rightarrow> \<tau>2" using fv context_invariance by auto
    then show ?thesis using same by simp
  next
    case False
    then show ?thesis sorry
  qed
next
  case (T_AppI e1 \<tau>1 \<tau>2 e2)
  then show ?case using T.T_AppI by (metis esubst_e.simps(3))
qed

end