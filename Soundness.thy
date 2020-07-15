theory Soundness
  imports Defs
begin

lemma list_minus_set: "set (list_minus e xs) = set e - set xs"
  by (induction e) (auto)

lemma free_in_context: "\<lbrakk> x \<in> set (fve_e e) ; \<Gamma> \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> \<exists>\<tau>'. (x, \<tau>') \<in> \<Gamma>"
proof (induction e arbitrary: \<Gamma> \<tau> x)
  case (Var y)
  then show ?case using T.cases by fastforce
next
  case (Lam y \<tau>' e)
  then have "x \<noteq> y" by (simp add: list_minus_set)
  then have x: "x \<in> set (fve_e e)" using list_minus_set T.cases Lam by fastforce
  from Lam(3) obtain \<tau>2 where "(y, \<tau>')#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<tau>' \<rightarrow> \<tau>2)" using T.cases by blast
  then show ?case using Lam(1)[OF x] by (meson \<open>x \<noteq> y\<close> isin.simps(2)) 
next
  case (App e1 e2)
  from App(4) obtain \<tau>1 \<tau>2 where e: "\<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>2 \<and> \<Gamma> \<turnstile> e2 : \<tau>1" using T.cases by blast
  from App have "x \<in> set (fve_e e1) \<or> x \<in> set (fve_e e2)" by simp
  then show ?case using e App by blast
next
  case Unit
  then show ?case by simp
next
  case (Let y e1 e2)
  then have x: "x \<in> set (fve_e e1) \<or> x \<in> set (fve_e e2)" using list_minus_set by fastforce
  from Let(4) obtain \<tau>1 where "\<Gamma> \<turnstile> e1 : \<tau>1 \<and> (y, \<tau>1)#\<Gamma> \<turnstile> e2 : \<tau>" using T.cases by blast
  then show ?case using x Let
    by (metis Diff_iff Un_iff fve_e.simps(5) isin.simps(2) list.set_intros(1) list_minus_set set_append)
qed

lemma fun_ty_lam: "\<lbrakk> is_v_of_e e ; \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  apply (cases e)
      apply auto
  using T.cases apply blast+
  done

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
      from \<open>is_v_of_e e1\<close> T_AppI(1) have "\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)" by (simp add: fun_ty_lam)
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
next
  case (T_LetI e1 \<tau>1 x e2 \<tau>2)
  then show ?case using ST_SubstI ST_LetI by blast
qed

definition closed :: "e \<Rightarrow> bool" where
  "closed x \<equiv> fve_e x = []"


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
next
  case (T_LetI e1 \<tau>1 x e2 \<tau>2)
  then show ?case apply auto
    by (smt DiffI T.T_LetI empty_iff insertE isin.simps(2) list.set(1) list.set(2) list_minus_set) 
qed

lemma substitution: "\<lbrakk> (x, \<tau>')#\<Gamma> \<turnstile> e : \<tau> ; [] \<turnstile> v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> esubst_e v x e : \<tau>"
proof (induction e arbitrary: \<Gamma> \<tau> v x \<tau>')
  case (Var y)
  then show ?case
  proof (cases "x = y")
    case True
    then have "\<tau> = \<tau>'" using Var T.cases by fastforce
    then show ?thesis using True Var context_invariance by fastforce
  next
    case False
    then show ?thesis using Var context_invariance by simp
  qed
next
  case (Lam y \<sigma> e)
  let ?lam = "\<lambda> y : \<sigma> . e"
  from Lam show ?case
  proof (cases "x = y")
    case True
    then have "esubst_e v x ?lam = ?lam" by simp
    then show ?thesis
      by (smt Diff_iff Lam.prems(1) True context_invariance fve_e.simps(2) insert_iff isin.simps(2) list.simps(15) list_minus_set)
  next
    case False
    then obtain \<tau>2 where P: "\<tau> = (\<sigma> \<rightarrow> \<tau>2)" using Lam(2) T.cases by blast
    then have "(y, \<sigma>)#(x, \<tau>')#\<Gamma> \<turnstile> e : \<tau>2" using T.cases Lam by blast
    then have "(x, \<tau>')#(y, \<sigma>)#\<Gamma> \<turnstile> e : \<tau>2" using context_invariance False by force
    then show ?thesis using False Lam T_AbsI P by simp
  qed
next
  case (App e1 e2)
  from \<open>(x, \<tau>') # \<Gamma> \<turnstile> App e1 e2 : \<tau>\<close> obtain \<tau>1 where P: "((x, \<tau>') # \<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>) \<and> ((x, \<tau>') # \<Gamma> \<turnstile> e2 : \<tau>1)" using T.cases by blast
  then show ?case using T_AppI App by fastforce
next
  case Unit
  then show ?case apply auto using T_UnitI T.cases by blast
next
  case (Let y e1 e2)
  from Let(3) obtain \<tau>1 where P: "(x, \<tau>')#\<Gamma> \<turnstile> e1 : \<tau>1 \<and> (y, \<tau>1)#(x, \<tau>')#\<Gamma> \<turnstile> e2 : \<tau>" using T.cases by blast
  from Let show ?case
  proof (cases "x = y")
    case True
    then have x: "esubst_e v x (Let y e1 e2) = Let y (esubst_e v x e1) e2" by simp
    then have e1: "\<Gamma> \<turnstile> esubst_e v x e1 : \<tau>1" using Let P by blast
    from True Let have e2: "(y, \<tau>1) # \<Gamma> \<turnstile> e2 : \<tau>" by (smt P context_invariance isin.simps(2))
    then show ?thesis using T_LetI[OF e1 e2] x by simp
  next
    case False
    then have "(x, \<tau>')#(y, \<tau>1)#\<Gamma> \<turnstile> e2 : \<tau>" using P context_invariance by fastforce
    then show ?thesis
      by (smt False Let.IH(1) Let.IH(2) Let.prems(2) P T_LetI empty_iff esubst_e.simps(5) list.set(1) set_ConsD)
  qed
qed

theorem preservation: "\<lbrakk> [] \<turnstile> e : \<tau> ; Step e e' \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
proof (induction "[] :: \<Gamma>" e \<tau> arbitrary: e' rule: T.induct)
case T_UnitI
  then show ?case using Step.cases by blast
next
  case (T_VarI x \<tau>)
  then show ?case using Step.cases by blast
next
  case (T_AbsI x \<tau>1 e \<tau>2)
  then show ?case using Step.cases by blast
next
  case (T_AppI e1 \<tau>1 \<tau>2 e2)
  from \<open>App e1 e2 \<longrightarrow> e'\<close> show ?case
  proof cases
    case (ST_BetaI x \<tau> e)
    then show ?thesis using substitution T.cases T_AppI by blast
  next
    case (ST_AppI e2)
    then show ?thesis using T_AppI T.T_AppI by blast
  next
    case (ST_App2I e2)
    then show ?thesis using T_AppI T.T_AppI by blast
  qed
next
  case (T_LetI e1 \<tau>1 x e2 \<tau>2)
  from \<open>Let x e1 e2 \<longrightarrow> e'\<close> show ?case
  proof (cases)
    case ST_SubstI
    then show ?thesis using substitution T.cases T_LetI by blast
  next
    case (ST_LetI e2)
    then show ?thesis using T_LetI T.T_LetI by blast
  qed
qed

definition stuck :: "e \<Rightarrow> bool" where
  "stuck e \<equiv> \<not>(is_v_of_e e \<or> (\<exists>e'. Step e e'))"

inductive Steps :: "e \<Rightarrow> e \<Rightarrow> bool" (infix "\<longrightarrow>*" 70) where
  refl: "Steps e e"
| trans: "\<lbrakk> Steps e1 e2 ; Step e2 e3 \<rbrakk> \<Longrightarrow> Steps e1 e3"

lemma multi_preservation: "\<lbrakk> e \<longrightarrow>* e' ; [] \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
  apply (induction e e' rule: Steps.induct)
  using preservation by blast+

corollary soundness: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow>* e' \<rbrakk> \<Longrightarrow> \<not>(stuck e')"
  unfolding stuck_def
  using progress multi_preservation by blast

end