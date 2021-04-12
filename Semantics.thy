theory Semantics
  imports Syntax Defs Lemmas
begin

no_notation HOL.implies (infixr "\<longrightarrow>" 25)

inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool" ("_ \<longrightarrow> _" 25) where

  ST_Beta: "App (\<lambda> x : \<tau> . e) e2 \<longrightarrow> e[e2/x]"

| ST_TBeta: "is_value e \<Longrightarrow> TApp (\<Lambda> a : k . e) \<tau> \<longrightarrow> e[\<tau>/a]"

| ST_TAbs: "e \<longrightarrow> e' \<Longrightarrow> (\<Lambda> a:k. e) \<longrightarrow> (\<Lambda> a:k. e')"

| ST_App: "e1 \<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<longrightarrow> App e1' e2"

| ST_TApp: "e \<longrightarrow> e' \<Longrightarrow> TApp e \<tau> \<longrightarrow> TApp e' \<tau>"

| ST_Let: "Let x \<tau> e1 e2 \<longrightarrow> e2[e1/x]"

| ST_Case_Cong: "e \<longrightarrow> e' \<Longrightarrow> Case e alts \<longrightarrow> Case e' alts"

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
proof (induction v rule: term.induct)
  case (App e1 e2)
  show ?case
  proof (rule ccontr)
    assume "\<not>beta_nf (App e1 e2)"
    then obtain e' where "App e1 e2 \<longrightarrow> e'" using beta_nf_def by blast
    then show "False" using App head_ctor_is_value beta_nf_def by cases auto
  qed
next
  case (TApp e \<tau>)
  show ?case
  proof (rule ccontr)
    assume "\<not>beta_nf (TApp e \<tau>)"
    then obtain e' where "TApp e \<tau> \<longrightarrow> e'" using beta_nf_def by blast
    then show "False" using TApp head_ctor_is_value beta_nf_def by cases auto
  qed
next
  case (Ctor D)
  then show ?case using Step.cases beta_nf_def by fastforce
next
  case (Lam x \<tau> e)
  then show ?case using Step.cases beta_nf_def by fastforce
next
  case (TyLam a k e)
  show ?case
  proof (rule ccontr)
    assume "\<not>beta_nf (\<Lambda> a:k. e)"
    then obtain e' where "(\<Lambda> a:k. e) \<longrightarrow> e'" using beta_nf_def by blast
    then show "False"
    proof cases
      case (ST_TAbs e2 e2' b)
      obtain c::tyvar where c:"atom c \<sharp> (a, e, b, e2)" by (rule obtain_fresh)
      then obtain e3 where 1: "[[atom b]]lst. e2 = [[atom c]]lst. e3" by (metis Abs_lst_rename fresh_PairD(2))
      then have 2: "e = (c \<leftrightarrow> a) \<bullet> e3" using ST_TAbs(1) c by (metis Abs_rename_body)
      from 1 have "e3 = (b \<leftrightarrow> c) \<bullet> e2" using Abs_rename_body by blast
      then have "e3 \<longrightarrow> (b \<leftrightarrow> c) \<bullet> e2'" using ST_TAbs(3) Step.eqvt by blast
      then have "e \<longrightarrow> (c \<leftrightarrow> a) \<bullet> (b \<leftrightarrow> c) \<bullet> e2'" using 2 Step.eqvt by blast
      then show ?thesis using TyLam beta_nf_def by auto
    qed
  qed
qed auto

lemma Step_deterministic: "\<lbrakk> e \<longrightarrow> e1 ; e \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> e1 = e2"
proof (induction e e1 arbitrary: e2 rule: Step.induct)
  case (ST_Beta v x \<tau> e)
  then show ?case
  proof cases
    case (ST_Beta y e')
    then show ?thesis using subst_term_same by blast
  next
    case (ST_App e')
    then show ?thesis using Step.cases by fastforce
  qed
next
  case outer: (ST_TAbs e e' a k)
  from outer(3) show ?case
  proof cases
    case (ST_TAbs e3 e3' b)
    obtain c::tyvar where "atom c \<sharp> (a, e, b, e3, e', e3')" by (rule obtain_fresh)
    then have c: "atom c \<sharp> (a, e, b, e3)" "atom c \<sharp> e'" "atom c \<sharp> e3'" by auto
    then obtain e4 where 1: "[[atom b]]lst. e3 = [[atom c]]lst. e4" by (metis Abs_lst_rename fresh_PairD(2))
    then have 2: "e = (c \<leftrightarrow> a) \<bullet> e4" using ST_TAbs(1) c by (metis Abs_rename_body)
    from 1 have 3: "e4 = (b \<leftrightarrow> c) \<bullet> e3" using c by (metis Abs_rename_body)

    have x1: "(\<Lambda> a : k . e') = (\<Lambda> c : k . (a \<leftrightarrow> c) \<bullet> e')" using c(2) Abs_lst_rename by fastforce
    have x2: "(\<Lambda> b : k . e3') = (\<Lambda> c : k. (b \<leftrightarrow> c) \<bullet> e3')" using c(3) Abs_lst_rename by fastforce

    let ?e4' = "(c \<leftrightarrow> a) \<bullet> (b \<leftrightarrow> c) \<bullet> e3'"
    from 3 have "e4 \<longrightarrow> (b \<leftrightarrow> c) \<bullet> e3'" using Step.eqvt ST_TAbs(3) by blast
    then have "e \<longrightarrow> ?e4'" using Step.eqvt 2 by blast
    then have "e' = ?e4'" using outer(2) by blast
    then have "(a \<leftrightarrow> c) \<bullet> e' = (b \<leftrightarrow> c) \<bullet> e3'" by (simp add: flip_commute)
    then show ?thesis using x1 x2 ST_TAbs(2) by argo
  qed
next
  case (ST_App e1 e2 e)
  from ST_App(3) show ?case
  proof cases
    case (ST_Beta x \<tau> e)
    then show ?thesis using ST_App.hyps beta_nf_def is_value.simps(2) value_beta_nf by blast
  next
    case (ST_App e2)
    then show ?thesis by (simp add: ST_App.IH)
  qed
next
  case (ST_Let v x e)
  then show ?case
  proof cases
    case (ST_Let x e)
    then show ?thesis using subst_term_same by blast
  qed
next
  case (ST_TBeta a e \<tau>)
  from ST_TBeta(2) show ?case
  proof cases
    case (ST_TBeta b e')
    then show ?thesis using subst_term_type_same by blast
  next
    case (ST_TApp e2)
    then show ?thesis using is_value.simps(3) value_beta_nf beta_nf_def ST_TBeta(1) by blast
  qed
next
  case (ST_TApp e1 e2 \<tau>)
  from ST_TApp(3) show ?case
    apply cases
    using ST_TApp value_beta_nf beta_nf_def by auto
qed

end
