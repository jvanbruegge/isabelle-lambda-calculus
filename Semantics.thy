theory Semantics
  imports Syntax Defs Lemmas
begin

no_notation HOL.implies (infixr "\<longrightarrow>" 25)

inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool" ("_ \<longrightarrow> _" 25) where
  ST_BetaI: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> App (\<lambda> x : \<tau> . e) v \<longrightarrow> subst_term v x e"

| ST_AppI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> App e1 e \<longrightarrow> App e2 e"

| ST_App2I: "\<lbrakk> is_value v ; e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> App v e1 \<longrightarrow> App v e2"

| ST_SubstI: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> Let x \<tau> v e \<longrightarrow> subst_term v x e"

| ST_LetI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> Let x \<tau> e1 e \<longrightarrow> Let x \<tau> e2 e"

| ST_BetaTI: "TyApp (\<Lambda> a . e) \<tau> \<longrightarrow> subst_term_type \<tau> a e"

| ST_AppTI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> TyApp e1 \<tau> \<longrightarrow> TyApp e2 \<tau>"
equivariance Step
nominal_inductive Step .

definition beta_nf :: "term \<Rightarrow> bool" where
  "beta_nf e \<equiv> \<nexists>e'. e \<longrightarrow> e'"

lemma value_beta_nf: "is_value v \<Longrightarrow> beta_nf v"
  apply (cases v rule: term.exhaust)
  using Step.cases beta_nf_def by fastforce+

lemma Step_deterministic: "\<lbrakk> e \<longrightarrow> e1 ; e \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> e1 = e2"
proof (induction e e1 arbitrary: e2 rule: Step.induct)
  case (ST_BetaI v x \<tau> e)
  from ST_BetaI(2) show ?case
  proof cases
    case (ST_BetaI y e')
    then show ?thesis using subst_term_same by blast
  next
    case (ST_AppI e')
    then show ?thesis using Step.cases by fastforce
  next
    case (ST_App2I e')
    then show ?thesis using ST_BetaI value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_AppI e1 e2 e)
  from ST_AppI(3) show ?case
    apply cases
    using ST_AppI Step.cases value_beta_nf beta_nf_def by fastforce+
next
  case (ST_App2I v e1 e2)
  from ST_App2I(4) show ?case
    apply cases
    using ST_App2I.hyps(2) value_beta_nf beta_nf_def apply blast
    using ST_App2I.hyps(1) value_beta_nf beta_nf_def apply blast
    using ST_App2I value_beta_nf beta_nf_def by auto
next
  case (ST_SubstI v x e)
  from ST_SubstI(2) show ?case
  proof cases
    case (ST_SubstI x e)
    then show ?thesis using subst_term_same by blast
  next
    case (ST_LetI e2 x e)
    then show ?thesis using ST_SubstI.hyps value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_LetI t1 t2 x \<tau> e)
  from ST_LetI(3) show ?case
    apply cases
    using ST_LetI value_beta_nf beta_nf_def by auto
next
  case (ST_BetaTI a e \<tau>)
  then show ?case
  proof cases
    case (ST_BetaTI b e')
    then show ?thesis using subst_term_type_same by blast
  next
    case (ST_AppTI e2)
    then show ?thesis using is_value.simps(3) value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_AppTI e1 e2 \<tau>)
  from ST_AppTI(3) show ?case
    apply cases
    using ST_AppTI value_beta_nf beta_nf_def by auto
qed

end