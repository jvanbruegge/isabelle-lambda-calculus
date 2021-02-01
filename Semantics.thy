theory Semantics
  imports Syntax Defs Lemmas
begin

no_notation HOL.implies (infixr "\<longrightarrow>" 25)

inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool" ("_ \<longrightarrow> _" 25) where

  ST_BetaI: "App (\<lambda> x : \<tau> . e) e2 \<longrightarrow> e[e2/x]"

| ST_AppI: "e1 \<longrightarrow> e2 \<Longrightarrow> App e1 e \<longrightarrow> App e2 e"

| ST_SubstI: "Let x \<tau> e1 e2 \<longrightarrow> e2[e1/x]"

| ST_BetaTI: "TApp (\<Lambda> a : k . e) \<tau> \<longrightarrow> e[\<tau>/a]"

| ST_CtorApp: "App (Ctor D tys vals) e \<longrightarrow> Ctor D tys (ECons e vals)"

| ST_CtorTApp: "TApp (Ctor D tys vals) \<tau> \<longrightarrow> Ctor D (TCons \<tau> tys) vals"

| ST_AppTI: "e1 \<longrightarrow> e2 \<Longrightarrow> TApp e1 \<tau> \<longrightarrow> TApp e2 \<tau>"
equivariance Step
nominal_inductive Step .

inductive Steps :: "term \<Rightarrow> term \<Rightarrow> bool" (infix "\<longrightarrow>*" 70) where
  refl: "e \<longrightarrow>* e"
| trans: "\<lbrakk> e1 \<longrightarrow>* e2 ; e2 \<longrightarrow> e3 \<rbrakk> \<Longrightarrow> Steps e1 e3"

definition beta_nf :: "term \<Rightarrow> bool" where
  "beta_nf e \<equiv> \<nexists>e'. e \<longrightarrow> e'"

definition stuck :: "term \<Rightarrow> bool" where
  "stuck e \<equiv> \<not>is_value e \<and> beta_nf e"

lemma value_beta_nf: "is_value v \<Longrightarrow> beta_nf v"
  apply (cases v rule: term_elist.exhaust(1))
  using Step.cases beta_nf_def by fastforce+

lemma Step_deterministic: "\<lbrakk> e \<longrightarrow> e1 ; e \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> e1 = e2"
proof (induction e e1 arbitrary: e2 rule: Step.induct)
  case (ST_BetaI v x \<tau> e)
  then show ?case
  proof cases
    case (ST_BetaI y e')
    then show ?thesis using subst_term_same by blast
  next
    case (ST_AppI e')
    then show ?thesis using Step.cases by fastforce
  qed
next
  case (ST_AppI e1 e2 e)
  from ST_AppI(3) show ?case
    apply cases
    using ST_AppI Step.cases value_beta_nf beta_nf_def by fastforce+
next
  case (ST_SubstI v x e)
  then show ?case
  proof cases
    case (ST_SubstI x e)
    then show ?thesis using subst_term_same by blast
  qed
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
next
  case (ST_CtorApp e D tys vals)
  then show ?case using beta_nf_def value_beta_nf by (cases rule: Step.cases) auto
next
  case (ST_CtorTApp D tys vals \<tau>)
  then show ?case using beta_nf_def value_beta_nf by (cases rule: Step.cases) auto
qed

end
