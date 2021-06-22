theory Typing
  imports Syntax Defs Defs2 Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

inductive Ax :: "\<Delta> \<Rightarrow> bool" ("\<turnstile> _")
  and Ctx :: "\<Delta> \<Rightarrow> \<Gamma> \<Rightarrow> bool" ("_ \<turnstile> _")
  and Ty :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool" ("_ , _ \<turnstile>\<^sub>t\<^sub>y _ : _") where

  Ax_Empty: "\<turnstile> []"

| Ax_Data: "\<lbrakk> \<turnstile> \<Delta> ; \<nexists>k. AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<turnstile> AxData T \<kappa> # \<Delta>"

| Ax_Ctor: "\<lbrakk> [] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; ctor_type \<tau> = Some (T, ks) ; \<nexists>t. AxCtor D t \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<turnstile> AxCtor D \<tau> # \<Delta>"

(* ------------------------------ *)

| Ctx_Empty: "\<turnstile> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> []"

| Ctx_TyVar: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> BTyVar a k # \<Gamma>"

| Ctx_Var: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> BVar x \<tau> # \<Gamma>"

(* ------------------------------ *)

| Ty_Var: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"

| Ty_App: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyApp \<tau>1 \<tau>2 : \<kappa>2"

| Ty_Data: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T : k"

| Ty_Arrow: "\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyArrow : \<star> \<rightarrow> \<star> \<rightarrow> \<star>"

| Ty_Forall: "\<lbrakk> BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (\<forall>a : k. \<sigma>) : \<star>"

equivariance Ax

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"

inductive Tm :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ , _ \<turnstile> _ : _" 50) and
          Alts :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> term \<Rightarrow> alt_list \<Rightarrow> \<tau> \<Rightarrow> bool" and
          Alt :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> term \<Rightarrow> alt \<Rightarrow> \<tau> \<Rightarrow> bool" where
  Tm_Var: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (Var x) : \<tau>"

| Tm_Abs: "BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2 \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| Tm_App: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> App e1 e2 : \<tau>2"

| Tm_TAbs: "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<sigma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (\<Lambda> a : k . e) : (\<forall> a : k . \<sigma>)"

| Tm_TApp: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<forall> a:k. \<sigma> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> TApp e \<tau> : \<sigma>[\<tau>/a]"

| Tm_Ctor: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxCtor D \<tau> \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Ctor D : \<tau>"

| Tm_Let: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 ; BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

| Tm_Case: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 ; head_data \<tau>1 = Some (T, \<sigma>s) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; exhaustive alts \<Delta> T ; Alts \<Gamma> \<Delta> e alts \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Case e alts : \<tau>"

| Alts_Nil: "Alts \<Gamma> \<Delta> e ANil \<tau>"

| Alts_Cons: "\<lbrakk> Alt \<Gamma> \<Delta> e alt \<tau> ; Alts \<Gamma> \<Delta> e alts \<tau> \<rbrakk> \<Longrightarrow> Alts \<Gamma> \<Delta> e (ACons alt alts) \<tau>"

| Alt_Ctor: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 ; head_data \<tau>1 = Some (T, \<sigma>s) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ;
               AxCtor K cty \<in> set \<Delta> ; ctor_type cty = Some (T, ks) ; subst_ctor cty \<sigma>s = Some args ;
               length vals = length args ; length tys = length ks ;
               zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma> , \<Delta> \<turnstile> e' : \<tau> \<rbrakk> \<Longrightarrow> Alt \<Gamma> \<Delta> e (MatchCtor K tys vals e') \<tau>"

equivariance Tm

lemmas Ax_intros = Ax_Ctx_Ty.intros(1-3)
lemmas Ctx_intros = Ax_Ctx_Ty.intros(4-6)
lemmas Ty_intros = Ax_Ctx_Ty.intros(7-11)

inductive_cases AxE[elim]:
  "\<turnstile> AxData T k # \<Delta>"
  "\<turnstile> AxCtor D \<tau> # \<Delta>"

inductive_cases CtxE[elim]:
  "\<Delta> \<turnstile> BTyVar a k # \<Gamma>"
  "\<Delta> \<turnstile> BVar x \<tau> # \<Gamma>"

inductive_cases TyE[elim!]:
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyApp \<tau>1 \<tau>2 : \<kappa>2"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData D : k"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyArrow : k"

inductive_cases TmE[elim!]:
  "\<Gamma> , \<Delta> \<turnstile> Var x : \<tau>"
  "\<Gamma> , \<Delta> \<turnstile> App e1 e2 : \<tau>2"
  "\<Gamma> , \<Delta> \<turnstile> TApp e \<tau> : \<tau>2"
  "\<Gamma> , \<Delta> \<turnstile> Ctor D : \<tau>"
  "\<Gamma> , \<Delta> \<turnstile> Case e alts : \<tau>"

inductive_cases AltsE[elim!]:
  "Alts \<Gamma> \<Delta> e (ACons alt alts) \<tau>"

(* Split induction principles *)
lemma Ty_induct[consumes 1, case_names Var App Data Arrow Forall]:
  fixes P::"\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool"
  assumes "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa>"
  and Var: "\<And>\<Gamma> \<Delta> a k. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyVar a) k"
  and App: "\<And>\<Gamma> \<Delta> \<tau>1 \<tau>2 \<kappa>1 \<kappa>2. \<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; P \<Gamma> \<Delta> \<tau>1 (KArrow \<kappa>1 \<kappa>2) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; P \<Gamma> \<Delta> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyApp \<tau>1 \<tau>2) \<kappa>2"
  and Data: "\<And>\<Delta> \<Gamma> T k. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyData T) k"
  and Arrow: "\<And>\<Gamma> \<Delta>. \<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P \<Gamma> \<Delta> TyArrow (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)"
  and Forall: "\<And>\<Gamma> \<Delta> a k \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; P (BTyVar a k # \<Gamma>) \<Delta> \<sigma> \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (\<forall> a:k. \<sigma>) \<star>"
shows "P \<Gamma> \<Delta> \<tau> \<kappa>"
  using Ax_Ctx_Ty.inducts(3)[OF assms(1), of "\<lambda>a. True" P "\<lambda>a b. True"] assms(2-6) by simp

lemma Tm_induct[consumes 1, case_names Var Abs App TAbs TApp Ctor Let Case]:
  fixes P::"\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool"
  assumes "\<Gamma> , \<Delta> \<turnstile> e : \<tau>"
  and "\<And>\<Gamma> \<Delta> x \<tau>. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (Var x) \<tau>"
  and "\<And>x \<tau>1 \<Gamma> \<Delta> e \<tau>2. \<lbrakk> BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2 ; P (BVar x \<tau>1 # \<Gamma>) \<Delta> e \<tau>2 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (\<lambda> x : \<tau>1 . e) (\<tau>1 \<rightarrow> \<tau>2)"
  and "\<And>\<Gamma> \<Delta> e1 \<tau>1 \<tau>2 e2. \<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>2 ; P \<Gamma> \<Delta> e1 (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>1 ; P \<Gamma> \<Delta> e2 \<tau>1 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (App e1 e2) \<tau>2"
  and "\<And>a k \<Gamma> \<Delta> e \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<sigma> ; P (BTyVar a k # \<Gamma>) \<Delta> e \<sigma> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (\<Lambda> a : k . e) (\<forall> a : k . \<sigma>)"
  and "\<And>\<Gamma> \<Delta> e a k \<sigma> \<tau>. \<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<forall> a : k . \<sigma> ; P \<Gamma> \<Delta> e (\<forall> a : k . \<sigma>) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TApp e \<tau>) \<sigma>[\<tau>/a]"
  and "\<And>\<Delta> \<Gamma> D \<tau>. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxCtor D \<tau> \<in> set \<Delta> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (Ctor D) \<tau>"
  and "\<And>\<Gamma> \<Delta> e1 \<tau>1 x e2 \<tau>2. \<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 ; P \<Gamma> \<Delta> e1 \<tau>1 ; BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>2 ; P (BVar x \<tau>1 # \<Gamma>) \<Delta> e2 \<tau>2 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (Let x \<tau>1 e1 e2) \<tau>2"
  and "\<And>\<Gamma> \<Delta> e \<tau>1 T \<sigma>s \<tau> alts. \<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 ; P \<Gamma> \<Delta> e \<tau>1 ; head_data \<tau>1 = Some (T, \<sigma>s) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; exhaustive alts \<Delta> T ; Alts \<Gamma> \<Delta> e alts \<tau> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (Case e alts) \<tau>"
shows "P \<Gamma> \<Delta> e \<tau>"
  using Tm_Alts_Alt.inducts(1)[OF assms(1), of _ "\<lambda>_ _ _ _ _. True" "\<lambda>_ _ _ _ _. True"] assms(2-9) by auto

(* axiom validity *)
lemma axioms_valid_aux:
  shows "\<Delta> \<turnstile> \<Gamma> \<longrightarrow> \<turnstile> \<Delta>"
  and "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<longrightarrow> \<turnstile> \<Delta>"
proof -
  have "(\<turnstile> \<Delta> \<longrightarrow> \<turnstile> \<Delta>) \<and> (\<Delta> \<turnstile> \<Gamma> \<longrightarrow> \<turnstile> \<Delta>) \<and> (\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<longrightarrow> \<turnstile> \<Delta>)"
    by (induction rule: Ax_Ctx_Ty.induct) (auto intro: Ax_intros)
  then show "\<Delta> \<turnstile> \<Gamma> \<longrightarrow> \<turnstile> \<Delta>" and "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<longrightarrow> \<turnstile> \<Delta>" by simp_all
qed
lemma axioms_valid_context: "\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> \<turnstile> \<Delta>"
  using axioms_valid_aux by simp
lemma axioms_valid_ty: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<Longrightarrow> \<turnstile> \<Delta>"
  using axioms_valid_aux by simp
lemma axioms_valid_tm: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> \<turnstile> \<Delta>"
  by (induction \<Gamma> \<Delta> e \<tau> rule: Tm_induct) (auto simp: axioms_valid_context axioms_valid_ty)
lemmas axioms_valid = axioms_valid_context axioms_valid_ty axioms_valid_tm

lemma Ctx_Ty_induct_split[case_names Ctx_Empty Ctx_TyVar Ctx_Var Ty_Var Ty_App Ty_Data Ty_Arrow Ty_Forall]:
  fixes P::"\<Delta> \<Rightarrow> \<Gamma> \<Rightarrow> bool" and Q::"\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool"
  assumes "\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P \<Delta> []"
  and "\<And>\<Gamma>' b k2. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; atom b \<sharp> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> P \<Delta> (BTyVar b k2 # \<Gamma>')"
  and "\<And>\<Gamma>' \<tau> x. \<lbrakk> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; Q \<Gamma>' \<Delta> \<tau> \<star> ; atom x \<sharp> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> P \<Delta> (BVar x \<tau> # \<Gamma>')"
  and "\<And>\<Gamma>' b k2. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; BTyVar b k2 \<in> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyVar b) k2"
  and "\<And>\<Gamma>' \<tau>1 \<kappa>1 \<kappa>2 \<tau>2. \<lbrakk> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; Q \<Gamma>' \<Delta> \<tau>1 (\<kappa>1 \<rightarrow> \<kappa>2) ; \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; Q \<Gamma>' \<Delta> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyApp \<tau>1 \<tau>2) \<kappa>2"
  and "\<And>\<Gamma>' T k. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyData T) k"
  and "\<And>\<Gamma>'. \<lbrakk> \<Delta> \<turnstile> (\<Gamma>' @ \<Gamma>) ; P \<Delta> \<Gamma>' \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> TyArrow (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)"
  and "\<And>\<Gamma>' b k2 \<sigma>. \<lbrakk> BTyVar b k2 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; Q (BTyVar b k2 # \<Gamma>') \<Delta> \<sigma> \<star> \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (\<forall> b : k2 . \<sigma>) \<star>"
shows "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Delta> \<Gamma>'"
  and "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<Delta> \<tau> k2"
proof -
  let ?\<Gamma> = "\<Gamma>' @ \<Gamma>"
  let ?P = "\<lambda>\<Delta>2 x. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma> \<and> \<Delta>2 = \<Delta>) \<longrightarrow> (P \<Delta> \<Gamma>2)"
  let ?Q = "\<lambda>x \<Delta>2 y z. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma> \<and> \<Delta>2 = \<Delta>) \<longrightarrow> (Q \<Gamma>2 \<Delta> y z)"

  have "(\<turnstile> \<Delta> \<longrightarrow> True) \<and> (\<Delta> \<turnstile> ?\<Gamma> \<longrightarrow> ?P \<Delta> ?\<Gamma>) \<and> (?\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> ?Q ?\<Gamma> \<Delta> \<tau> k2)"
  proof (cases rule: Ax_Ctx_Ty.induct[of "\<lambda>x. True" "?Q" "?P"])
    case (Ctx_Empty \<Delta>)
    then show ?case
    proof (auto, goal_cases)
      case 1
      then show ?case using assms(1) Ax_Ctx_Ty.Ctx_Empty[OF Ctx_Empty(1)] by simp
    qed
  next
    case (Ctx_TyVar \<Delta>2 \<Gamma>' a k)
    then show ?case
    proof (auto, goal_cases)
      case (1 \<Gamma>2)
      then show ?case
      proof (cases "\<Gamma>2 = []")
        case True
        then have "\<Delta> \<turnstile> \<Gamma>" using Ax_Ctx_Ty.Ctx_TyVar[OF Ctx_TyVar(1,3)] 1 by auto
        then show ?thesis using assms(1) True by simp
      next
        case False
        then obtain G where "\<Gamma>' = G @ \<Gamma>" by (meson Cons_eq_append_conv 1)
        then show ?thesis using assms(2) Ctx_TyVar 1 by auto
      qed
    qed
  next
    case (Ctx_Var \<Gamma>' \<Delta>2 \<tau> x)
    then show ?case
    proof (auto, goal_cases)
      case (1 \<Gamma>2)
      then show ?case
      proof (cases "\<Gamma>2 = []")
        case True
        then have "\<Delta> \<turnstile> \<Gamma>" using Ax_Ctx_Ty.Ctx_Var[OF Ctx_Var(1,3)] 1 by simp
        then show ?thesis using True assms(1) by simp
      next
        case False
        then obtain G where "\<Gamma>' = G @ \<Gamma>" by (meson Cons_eq_append_conv 1)
        then show ?thesis using assms(3) Ctx_Var 1 by auto
      qed
    qed
  qed (auto simp: assms(1,4-8))

  then show "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Delta> \<Gamma>'" and "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<Delta> \<tau> k2" by simp_all
qed

(* context validity *)
lemma context_valid_ty: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
  by (induction \<Gamma> \<Delta> \<tau> \<kappa> rule: Ty_induct) auto
lemma context_valid_tm: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
  by (induction \<Gamma> \<Delta> e \<tau> rule: Tm_induct) (auto simp: context_valid_ty)
lemmas context_valid = context_valid_ty context_valid_tm

lemma supp_in_context_ty: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<Longrightarrow> supp \<tau> \<subseteq> supp \<Gamma>"
proof (induction \<Gamma> \<Delta> \<tau> k rule: Ty_induct)
  case (Var \<Gamma> \<Delta> a k)
  then show ?case by (metis \<tau>.supp(1) fresh_def fresh_not_isin_tyvar singletonD subsetCI supp_at_base)
next
  case (Forall \<Gamma> \<Delta> a k \<sigma>)
  from Forall(2) show ?case unfolding supp_Cons binder.supp(2) \<tau>.supp(5) pure_supp supp_at_base by auto
qed (auto simp: \<tau>.supp pure_supp)

corollary fresh_in_context_ty: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
  unfolding fresh_def using supp_in_context_ty by blast

lemma axioms_cons_valid[elim]: "\<turnstile> ax # \<Delta> \<Longrightarrow> (\<turnstile> \<Delta> \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases rule: Ax.cases) (auto simp: axioms_valid(2))

lemma axioms_empty_supp: "\<turnstile> \<Delta> \<Longrightarrow> supp \<Delta> = {}"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
  proof (cases a rule: axiom.exhaust)
    case (AxData D k)
    then show ?thesis by (metis AxE(1) Cons.IH Cons.prems axiom.supp(1) pure_supp supp_Cons)
  next
    case (AxCtor K \<tau>)
    then have "[] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using Cons by blast
    then have 1: "supp \<tau> = {}" using supp_in_context_ty supp_Nil by blast
    have 2: "supp \<Delta> = {}" using Cons by auto
    then show ?thesis using 1 AxCtor axiom.supp(2) pure_supp unfolding supp_Cons by blast
  qed
qed (simp add: supp_Nil)

corollary fresh_in_axioms: "\<turnstile> \<Delta> \<Longrightarrow> atom (a::tyvar) \<sharp> \<Delta>"
  unfolding fresh_def using axioms_empty_supp by simp
corollary permute_axioms[simp]: "\<turnstile> \<Delta> \<Longrightarrow> p \<bullet> \<Delta> = \<Delta>"
  using axioms_empty_supp by (simp add: fresh_star_def supp_perm_eq)

nominal_inductive Ax avoids
  Ty_Forall: a
proof goal_cases
  case (1 a k \<Gamma> \<Delta> \<sigma>)
  then have "\<Delta> \<turnstile> BTyVar a k # \<Gamma>" by (rule context_valid(1))
  then have 2: "atom a \<sharp> \<Gamma>" by blast
  have 3: "atom a \<sharp> \<Delta>" by (rule fresh_in_axioms[OF axioms_valid(2)[OF 1]])
  obtain c \<sigma>' where 4: "(\<forall> a:k. \<sigma>) = (\<forall> c:k. \<sigma>') \<and> atom a \<sharp> (\<forall> c:k. \<sigma>')" using Abs_fresh_var by auto
  then have "atom a \<sharp> (\<Gamma>, \<Delta>, \<forall> c:k. \<sigma>', \<star>)" using 2 3 fresh_Pair by simp
  then show ?case using 2 fresh_star_def by fastforce
qed auto

lemma var_strengthen_aux:
  shows "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<longrightarrow> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma>"
  and "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
proof (induction rule: Ctx_Ty_induct_split)
  case Ctx_Empty
  then show ?case using context_valid(1) by auto
next
  case (Ctx_TyVar \<Gamma>' b k2)
  then show ?case by (metis Ctx.simps append_Cons fresh_Cons fresh_append)
next
  case (Ctx_Var \<Gamma>' \<tau> x)
  then have "atom x \<sharp> \<Gamma>' @ \<Gamma>" using fresh_append fresh_Cons by blast
  then show ?case using Ctx_intros(3)[OF Ctx_Var(2)] by simp
next
  case (Ty_Var \<Gamma>' b k2)
  then have "BTyVar b k2 \<in> (\<Gamma>' @ \<Gamma>)" using strengthen_isin_tyvar by simp
  then show ?case by (rule Ty_intros(1)[OF Ty_Var(2)])
qed (auto intro: Ty_intros)
lemma var_strengthen_context: "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma>"
  using var_strengthen_aux by simp
lemma var_strengthen_ty: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
  using var_strengthen_aux by simp
lemmas strengthen = var_strengthen_context var_strengthen_ty

lemma context_cons_valid[elim]: "(\<Delta>::\<Delta>) \<turnstile> bndr # \<Gamma> \<Longrightarrow> (\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases rule: Ctx.cases) (auto simp: context_valid(1))

lemma isin_subset:
  fixes \<Gamma>::"\<Gamma>"
  assumes "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma>"
  shows "bndr \<in> \<Gamma> \<longrightarrow> bndr \<in> (\<Gamma>' @ \<Gamma>)"
proof
  assume "bndr \<in> \<Gamma>"
  then show "bndr \<in> (\<Gamma>' @ \<Gamma>)"
  using assms proof (induction \<Gamma>' arbitrary: \<Gamma>)
    case (Cons b \<Gamma>2)
    have 1: "\<Delta> \<turnstile> \<Gamma>2 @ \<Gamma>" using Cons(3) by auto
    have 2: "bndr \<in> (\<Gamma>2 @ \<Gamma>)" by (rule Cons(1)[OF Cons(2) 1])
    show ?case
    proof (cases b rule: binder.exhaust)
      case (BVar x \<tau>)
      then have "atom x \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons by auto
      then show ?thesis using 2 BVar fresh_not_isin_var by (cases bndr rule: binder.exhaust) auto
    next
      case (BTyVar a k)
      then have "atom a \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons by auto
      then show ?thesis using 2 BTyVar fresh_not_isin_tyvar by (cases bndr rule: binder.exhaust) auto
    qed
  qed auto
qed

lemma Ty_Forall_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (\<forall>a:k. \<sigma>) : \<tau>" and b: "atom a \<sharp> \<Gamma>"
  shows "BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<and> \<tau> = \<star>"
proof (cases rule: Ty.cases[OF a])
  case (5 a' k' \<Gamma>' \<Delta>' \<sigma>')
  then have 1: "(BTyVar a' k # \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" by simp
  have valid: "\<turnstile> \<Delta>" by (rule axioms_valid(2)[OF 1])
  have "(a' \<leftrightarrow> a) \<bullet> \<sigma>' = \<sigma>" using Abs_rename_body[of a' \<sigma>' a \<sigma>] 5(3) by auto
  then have 2: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using Ty.eqvt[OF 1, of "(a' \<leftrightarrow> a)"] valid by auto
  have 3: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # ((a' \<leftrightarrow> a) \<bullet> \<Gamma>)" using Cons_eqvt flip_fresh_fresh by force
  have 4: "(a' \<leftrightarrow> a) \<bullet> \<Gamma> = \<Gamma>" by (metis 5(1,5) CtxE(1) b context_valid_ty flip_def swap_fresh_fresh)
  show ?thesis using 2 3 4 5(4) by argo
qed simp_all

lemma weaken_isin: "\<lbrakk> bndr \<in> (\<Gamma> @ \<Gamma>') ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> bndr \<in> (\<Gamma> @ xs @ \<Gamma>')"
proof (induction \<Gamma> arbitrary: bndr \<Gamma>' xs)
  case Nil
  then show ?case by (cases bndr rule: binder.exhaust) (auto simp: isin_subset)
next
  case (Cons b \<Gamma>)
  have 1: "\<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>'" using Cons(3) Ctx.cases by auto
  then show ?case
  proof (cases b rule: binder.exhaust)
    case (BVar x \<tau>)
    then show ?thesis using 1 Cons by (cases bndr rule: binder.exhaust) auto
  next
    case (BTyVar a k)
    then show ?thesis using 1 Cons by (cases bndr rule: binder.exhaust) auto
  qed
qed

lemma weaken_ty: "\<lbrakk> \<Gamma> @ \<Gamma>' , \<Delta>  \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
proof (nominal_induct \<tau> avoiding: \<Gamma> \<Gamma>' xs k rule: \<tau>.strong_induct)
  case (TyVar x)
  have 1: "BTyVar x k \<in> (\<Gamma> @ \<Gamma>')" by (cases rule: Ty.cases[OF TyVar(1)]) auto
  show ?case by (rule Ty_Var[OF TyVar(2) weaken_isin[OF 1 TyVar(2)]])
next
  case (TyData T)
  then have "AxData T k \<in> set \<Delta>" by blast
  then show ?case by (rule Ty_Data[OF TyData(2)])
next
  case TyArrow
  then have "k = (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)" by blast
  then show ?case using Ty_Arrow[OF TyArrow(2)] by argo
next
  case (TyApp \<tau>1 \<tau>2)
  then obtain k1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : k1 \<rightarrow> k" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by blast
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : k1 \<rightarrow> k" by (rule TyApp(1)[OF P(1) TyApp(4)])
  have 3: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by (rule TyApp(2)[OF P(2) TyApp(4)])
  show ?case by (rule Ty_App[OF 2 3])
next
  case (TyForall a k1 \<sigma>)
  have P: "(BTyVar a k1 # \<Gamma>) @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" "k = \<star>" using Ty_Forall_Inv[OF TyForall(6)] TyForall(1,2) fresh_append by auto
  have 1: "atom a \<sharp> \<Gamma> @ xs @ \<Gamma>'" using TyForall(1-3) fresh_append by blast
  have 2: "\<Delta> \<turnstile> (BTyVar a k1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_TyVar[OF TyForall(7) 1] by simp
  have 3: "BTyVar a k1 # \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using TyForall(5)[OF P(1) 2] by simp
  show ?case using Ty_Forall[OF 3] P(2) by simp
qed

lemma weaken_axioms_ty: "\<lbrakk> \<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; \<Delta>' @ xs @ \<Delta> \<turnstile> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> ,  \<Delta>' @ xs @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
proof (nominal_induct \<tau> avoiding: \<Delta> \<Delta>' k xs \<Gamma> rule: \<tau>.strong_induct)
  case (TyApp \<tau>1 \<tau>2)
  then show ?case using Ty_App by blast
next
  case (TyForall a k1 \<sigma>)
  have P: "BTyVar a k1 # \<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" "k = \<star>" using Ty_Forall_Inv[OF TyForall(7,5)] by auto
  have 1: "BTyVar a k1 # \<Gamma> , \<Delta>' @ xs @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" by (rule TyForall(6)[OF P(1) Ctx_TyVar[OF TyForall(8,5)]])
  show ?case using Ty_Forall[OF 1] P(2) by argo
qed (auto intro: Ty_intros)
lemmas weaken = weaken_isin weaken_ty weaken_axioms_ty

(* inversion rules for abstractions *)
lemma T_Abs_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  obtains \<tau>2 where "BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" "\<tau> = arrow_app \<tau>1 \<tau>2"
proof (cases rule: Tm.cases[OF a])
  case (2 x' \<tau>1' \<Gamma>' \<Delta>' e' \<tau>2)
  then have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" using Abs_rename_body[of x' e' x e] by auto
  have valid: "\<turnstile> \<Delta>" using axioms_valid(3)[OF 2(5)] 2(2) by simp
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 2 swap that by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 2 fresh_Cons)
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) , \<Delta> \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using 2 Tm.eqvt[OF 2(5), of "(x' \<leftrightarrow> x)"] by fastforce
    have "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>)) = BVar x \<tau>1 # \<Gamma>"
      by (metis "1" "2"(1) "2"(5) CtxE(2) binder.perm_simps(1) context_valid_tm flip_at_simps(1) flip_fresh_fresh fresh_Cons perm_\<tau>_vars)
    then show ?thesis using 1 2 3 swap that by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>"
proof (cases rule: Tm.cases[OF a])
  case (7 \<Gamma>' \<Delta>' e1' \<tau>1' x' e2' \<tau>2')
  have swap: "(x' \<leftrightarrow> x) \<bullet> e2' = e2" using Abs_rename_body[of x' e2' x e2] 7(3) by simp
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 7 swap by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1 # \<Gamma>'" using b by (simp add: 7 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) , \<Delta> \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using Tm.eqvt[OF 7(6), of "(x' \<leftrightarrow> x)"] 7 by auto
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "1" 7(1,6) CtxE(2) binder.perm_simps(1) context_valid_tm flip_at_simps(1) flip_def fresh_Cons perm_\<tau>_vars swap_fresh_fresh)
    from 2 3 7 swap show ?thesis by auto
  qed
qed simp_all

lemma T_AbsT_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> (\<Lambda> a : k . e) : \<tau>" and b: "atom a \<sharp> \<Gamma>" "atom a \<sharp> \<tau>"
  obtains \<sigma> where "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a:k. \<sigma>)"
proof (cases rule: Tm.cases[OF a])
  case (4 a' k' \<Gamma>' \<Delta>' e' \<sigma>')
  then have fresh: "atom a' \<sharp> \<Gamma>" by (cases rule: Ctx.cases[OF context_valid(2)[OF 4(5)]]) auto
  have swap: "(a' \<leftrightarrow> a) \<bullet> e' = e" using Abs_rename_body[of a' e' a e] 4(3) by simp
  have valid: "\<turnstile> \<Delta>" using axioms_valid(3)[OF 4(5)] 4(2) by simp
  show ?thesis
  proof (cases "atom a = atom a'")
    case True
    then show ?thesis by (metis 4 Abs1_eq_iff(3) atom_eq_iff term_alt_list_alt.eq_iff(6) that)
  next
    case False
    then have 1: "atom a \<sharp> BTyVar a' k # \<Gamma>" using b by (simp add: 4 fresh_Cons)
    have 2: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)), \<Delta> \<turnstile> (a' \<leftrightarrow> a) \<bullet> e' : (a' \<leftrightarrow> a) \<bullet> \<sigma>'" using Tm.eqvt[OF 4(5), of "(a' \<leftrightarrow> a)"] valid 4 by auto
    have "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = ((a' \<leftrightarrow> a) \<bullet> BTyVar a' k) # \<Gamma>" using 1 fresh flip_fresh_fresh b(1) by simp
    then have "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # \<Gamma>" by (simp add: flip_fresh_fresh)
    then have "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : (a' \<leftrightarrow> a) \<bullet> \<sigma>'" using 2 swap by argo
    then show ?thesis by (metis "4"(3,4) Abs1_eq_iff(3) False \<tau>.eq_iff(5) \<tau>.fresh(5) b(2) empty_iff flip_commute insert_iff list.set(1,2) term_alt_list_alt.eq_iff(6) that)
  qed
qed simp_all

lemma zip_with_context_fresh_vars: "\<lbrakk> \<Delta> \<turnstile> zip_with BVar vars xs @ \<Gamma> ; length vars \<le> length xs \<rbrakk> \<Longrightarrow> set (map atom vars) \<sharp>* \<Gamma>"
proof (induction vars arbitrary: xs)
  case Nil
  then show ?case using fresh_star_def by auto
next
  case (Cons a vars)
  then obtain x xs' where P: "xs = x # xs'" by (cases xs) auto
  then have 1: "length vars \<le> length xs'" using Cons by simp
  let ?\<Gamma> = "zip_with BVar vars xs' @ \<Gamma>"
  from P have "\<Delta> \<turnstile> BVar a x # ?\<Gamma>" using Cons(2) by simp
  then have "?\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x : \<star>" and 2:"atom a \<sharp> ?\<Gamma>" by auto
  then have 3: "\<Delta> \<turnstile> ?\<Gamma>" using context_valid(1) by simp
  show ?case using Cons(1)[OF 3 1] 2 fresh_append
    by (metis (no_types, lifting) fresh_star_def list.simps(9) set_ConsD)
qed

lemma zip_with_context_fresh_tyvars: "\<lbrakk> \<Delta> \<turnstile> zip_with BTyVar tys xs @ \<Gamma> ; length tys \<le> length xs \<rbrakk> \<Longrightarrow> set (map atom tys) \<sharp>* \<Gamma>"
proof (induction tys arbitrary: xs)
  case Nil
  then show ?case using fresh_star_def by auto
next
  case (Cons a vars)
  then obtain x xs' where P: "xs = x # xs'" by (cases xs) auto
  then have 1: "length vars \<le> length xs'" using Cons by simp
  let ?\<Gamma> = "zip_with BTyVar vars xs' @ \<Gamma>"
  from P have "\<Delta> \<turnstile> BTyVar a x # ?\<Gamma>" using Cons(2) by simp
  then have 3: "\<Delta> \<turnstile> ?\<Gamma>" "atom a \<sharp> ?\<Gamma>" by auto
  show ?case using Cons(1)[OF 3(1) 1] 3(2) fresh_append
    by (metis (no_types, lifting) fresh_star_def list.simps(9) set_ConsD)
qed

lemma context_valid_append: "\<Delta>::\<Delta> \<turnstile> \<Gamma>' @ \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
proof (induction \<Gamma>')
  case (Cons a \<Gamma>')
  then show ?case using context_valid(1) by (cases a rule: binder.exhaust) auto
qed auto

lemma axioms_split_valid: "\<turnstile> \<Delta>' @ \<Delta> \<Longrightarrow> \<turnstile> \<Delta>"
proof (induction \<Delta>')
  case (Cons a \<Delta>')
  then show ?case using axioms_valid(2) by (cases a rule: axiom.exhaust) auto
qed simp

lemma axioms_regularity: "\<turnstile> \<Delta>' @ AxCtor D \<tau> # \<Delta> \<Longrightarrow> [] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>"
  using Ax_Ctor axioms_split_valid by (induction \<Delta>) blast+

lemma context_regularity: "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>"
  using Ctx_Var context_valid_append by (induction \<Gamma>) blast+

lemma isin_same_kind: "\<lbrakk> BTyVar a k1 \<in> (\<Gamma>' @ BTyVar a k2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BTyVar a k2 # \<Gamma> \<rbrakk> \<Longrightarrow> k1 = k2"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case by (cases rule: Ctx.cases[OF Cons(3)]) (auto split: if_splits simp: fresh_Cons fresh_append fresh_at_base(2))
qed auto

lemma isin_same_type: "\<lbrakk> BVar x \<tau> \<in> (\<Gamma>' @ BVar x \<tau>2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau>2 # \<Gamma> \<rbrakk> \<Longrightarrow> \<tau> = \<tau>2"
proof (induction \<Gamma>')
  case (Cons a \<Gamma>')
  then show ?case by (cases rule: Ctx.cases[OF Cons(3)]) (auto split: if_splits simp: fresh_Cons fresh_append fresh_at_base)
qed auto
lemmas isin_same = isin_same_kind isin_same_type

lemma isin_subst_tyvar: "\<lbrakk> BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BTyVar b k2 # \<Gamma> ; a \<noteq> b \<rbrakk> \<Longrightarrow> BTyVar a k \<in> (\<Gamma>'[\<sigma>/b] @ \<Gamma>)"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case
  proof (cases rule: Ctx.cases[OF Cons(3)])
    case (2 \<Gamma>2 c k3)
    then have "BTyVar a k = bndr \<or> BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>)" by (metis Cons.prems(1) Cons_eq_append_conv isin.simps(5) list.inject)
    then show ?thesis
    proof
      assume a: "BTyVar a k = bndr"
      then show ?thesis using 2 Cons by auto
    next
      assume "BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>)"
      then show ?thesis using 2 Cons fresh_not_isin_tyvar by auto
    qed
  next
    case (3 \<Gamma> \<tau> x)
    then show ?thesis using Cons by auto
  qed simp
qed simp

lemma axiom_isin_split: "\<lbrakk> b \<in> set \<Delta> ; \<turnstile> \<Delta> \<rbrakk> \<Longrightarrow> \<exists>\<Delta>1 \<Delta>2. \<Delta> = \<Delta>1 @ b # \<Delta>2"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
  proof (cases "a = b")
    case True
    then show ?thesis by blast
  next
    case False
    then show ?thesis by (meson Cons.prems(1) split_list)
  qed
qed simp

lemma type_substitution_aux:
  assumes "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
  shows "(\<Delta> \<turnstile> (\<Gamma>' @ BTyVar a k # \<Gamma>) \<longrightarrow> \<Delta> \<turnstile> (subst_context \<Gamma>' \<sigma> a @ \<Gamma>))"
    and "(\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> subst_context \<Gamma>' \<sigma> a @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y subst_type \<tau> \<sigma> a : k2)"
proof (induction rule: Ctx_Ty_induct_split)
  case Ctx_Empty
  then show ?case using context_valid(1)[OF assms] by simp
next
  case (Ctx_TyVar \<Gamma>' b k2)
  then have "atom b \<sharp> \<sigma>" using assms fresh_Cons fresh_append fresh_in_context_ty by blast
  then have 1: "atom b \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson Ctx_TyVar(3) fresh_Cons fresh_append fresh_subst_context_tyvar)
  show ?case using Ax_Ctx_Ty.Ctx_TyVar[OF Ctx_TyVar(2) 1] assms by auto
next
  case (Ctx_Var \<Gamma>' \<tau> x)
  have 1: "atom x \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson Ctx_Var(3) fresh_Cons fresh_append fresh_subst_context_var)
  show ?case using Ax_Ctx_Ty.Ctx_Var[OF Ctx_Var(2) 1] by simp
next
  case (Ty_Var \<Gamma>' b k2)
  then show ?case
    proof (cases "b = a")
    case True
    then have "k = k2" using isin_same(1) Ty_Var by blast
    then have "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (TyVar b)[\<sigma>/a] : k2" using True assms(1) by simp
    then show ?thesis using weaken_ty[of "[]"] Ty_Var(2) by auto
  next
    case False
    have 1: "BTyVar b k2 \<in> (\<Gamma>'[\<sigma>/a] @ \<Gamma>)" by (rule isin_subst_tyvar[OF Ty_Var(3,1) False])
    show ?thesis using Ax_Ctx_Ty.Ty_Var[OF Ty_Var(2) 1] False by simp
  qed
next
  case (Ty_Forall \<Gamma>' b k2 \<sigma>')
  have 1: "a \<noteq> b" by (metis CtxE(1) Ty_Forall(1) binder.fresh(2) context_valid_ty fresh_Cons fresh_append fresh_at_base(2))
  then have 2: "BTyVar b k2 # \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<sigma>/a] : \<star>" using Ty_Forall(2) by simp
  show "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (\<forall> b : k2 . \<sigma>')[\<sigma>/a] : \<star>" using Ax_Ctx_Ty.Ty_Forall[OF 2]
    by (metis "1" "2" CtxE(1) assms atom_eq_iff context_valid_ty fresh_Pair fresh_append fresh_at_base(2) fresh_in_context_ty subst_type.simps(5))
qed (auto intro: Ty_intros)
corollary type_substitution_context: "\<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ BTyVar a k # \<Gamma> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>"
  using type_substitution_aux by blast
corollary type_substitution_ty: "\<lbrakk> \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>[\<sigma>/a] : k2"
  using type_substitution_aux by blast

lemma typing_regularity: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>"
proof (induction \<Gamma> \<Delta> e \<tau> rule: Tm_induct)
  case (Var \<Gamma> \<Delta> x \<tau>)
  then obtain \<Gamma>1 \<Gamma>2 where 1: "\<Gamma> = \<Gamma>1 @ BVar x \<tau> # \<Gamma>2" using isin_split by blast
  then have "\<Gamma>2 , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using context_regularity Var(1) by blast
  then show ?case using weaken_ty[of "[]" \<Gamma>2 \<Delta> \<tau> \<star> "\<Gamma>1 @ [BVar x \<tau>]"] Var(1) 1 by simp
next
  case (Abs x \<tau>1 \<Gamma> \<Delta> e \<tau>2)
  have 1: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using context_regularity context_valid(1)[OF Abs(2)] by blast
  have 2: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" using strengthen(2)[of "[]"] Abs(2) by force
  have 3: "\<Delta> \<turnstile> \<Gamma>" by (rule context_valid(1)[OF 1])
  show ?case by (rule Ty_App[OF Ty_App[OF Ty_Arrow[OF 3] 1] 2])
next
  case (TApp \<Gamma> \<Delta> e a k \<sigma> \<tau>)
  obtain a' \<sigma>' where P: "(\<forall> a:k. \<sigma>) = (\<forall> a':k. \<sigma>')" "BTyVar a' k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" by (cases rule: Ty.cases[OF TApp(3)]) auto
  have "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<tau>/a'] : \<star>" using type_substitution_ty[of "[]", OF _ TApp(2)] P by auto
  then show ?case using P(1) subst_type_same by auto
next
  case (Ctor \<Delta> \<Gamma> D \<tau>)
  from Ctor(1) have 1: "\<turnstile> \<Delta>" by (rule axioms_valid(1))
  then obtain \<Delta>1 \<Delta>2 where 2: "\<Delta> = \<Delta>1 @ AxCtor D \<tau> # \<Delta>2" using axiom_isin_split[OF Ctor(2) 1] by blast
  then have "[] , \<Delta>2 \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using axioms_regularity 1 by blast
  then have "[] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using weaken(3)[of "[]" "[]" \<Delta>2 \<tau> \<star> "\<Delta>1 @ [AxCtor D \<tau>]"] 1 2 Ctx_Empty by simp
  then show ?case using weaken(2)[of "[]" "[]"] Ctor(1) by simp
next
  case (Let \<Gamma> e1 \<tau>1 x e2 \<tau>2)
  then show ?case using strengthen(2)[of "[]"] by force
qed (auto intro: Ty_intros)

corollary supp_cty: "\<lbrakk> \<turnstile> \<Delta> ; AxCtor K cty \<in> set \<Delta> \<rbrakk> \<Longrightarrow> supp cty = {}"
  using axioms_empty_supp by (metis axiom.supp(2) axioms_split_valid split_list sup_bot.neutr_eq_iff supp_Cons) 

lemma supp_args:
  assumes "\<Gamma> , \<Delta> \<turnstile> e : \<tau>1" "head_data \<tau>1 = Some (T, \<sigma>s)" "AxCtor K cty \<in> set \<Delta>" "subst_ctor cty \<sigma>s = Some args"
  shows "supp args \<subseteq> supp \<Gamma>"
proof -
  have 1: "supp cty = {}" by (rule supp_cty[OF axioms_valid(3)[OF assms(1)] assms(3)])
  have "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule typing_regularity[OF assms(1)])
  then have "supp \<tau>1 \<subseteq> supp \<Gamma>" by (rule supp_in_context_ty)
  then have "supp \<sigma>s \<subseteq> supp \<Gamma>" using supp_head_data[OF assms(2)] by simp
  then show "supp args \<subseteq> supp \<Gamma>" using supp_subst_ctor[OF assms(4)] 1 by simp
qed

lemma Alt_Ctor_Inv: 
  assumes a: "Alt \<Gamma> \<Delta> e (MatchCtor K tys vals e') \<tau>"
  and fresh: "set (map atom tys) \<sharp>* \<Gamma>" "set (map atom vals) \<sharp>* \<Gamma>" "set (map atom tys) \<sharp>* \<tau>"
obtains \<tau>1 T \<sigma>s cty ks args where "\<Gamma> , \<Delta> \<turnstile> e : \<tau>1" "head_data \<tau>1 = Some (T, \<sigma>s)" "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" "AxCtor K cty \<in> set \<Delta>" "ctor_type cty = Some (T, ks)"
  "length args = length vals" "length ks = length tys"
  "subst_ctor cty \<sigma>s = Some args" "zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma> , \<Delta> \<turnstile> e' : \<tau>"
proof (cases rule: Alt.cases[OF a])
  case (1 \<Gamma>2 \<Delta>2 e2 \<tau>1 T \<sigma>s \<tau>2 K2 cty ks args vals2 tys2 e'2)
  let ?tys = "map atom tys" and ?vals = "map atom vals"
  let ?tys2 = "map atom tys2" and ?vals2 = "map atom vals2"
  from 1 have 2: "[?tys2 @ ?vals2]lst. e'2 = [?tys @ ?vals]lst. e'" by simp
  from 1 have valid: "\<Delta> \<turnstile> zip_with BVar vals2 args @ zip_with BTyVar tys2 ks @ \<Gamma>" using context_valid(2) by simp
  then have valid_axioms: "\<turnstile> \<Delta>" by (rule axioms_valid(1))

  have g1: "set ?vals2 \<sharp>* \<Gamma>" using zip_with_context_fresh_vars[OF valid] 1(12) fresh_append by (simp add: fresh_star_list(1))
  have g2: "set ?tys2 \<sharp>* \<Gamma>" using zip_with_context_fresh_tyvars valid context_valid_append 1(13) by (metis order_refl)
  then have g: "set (?tys2 @ ?vals2) \<sharp>* \<Gamma>" using g1 using fresh_star_Un by auto 

  obtain p where P: "p \<bullet> e'2 = e'" "p \<bullet> (?tys2 @ ?vals2) = ?tys @ ?vals" "supp p \<subseteq> set (?tys2 @ ?vals2) \<union> set (?tys @ ?vals)" by (rule Abs_rename_body_star[OF 2])
  have G: "supp \<Gamma> \<inter> supp p = {}" using g fresh(1-2) P(3) unfolding fresh_star_def fresh_def using UnE disjoint_iff set_append subsetD by auto
  then have 3: "p \<bullet> \<Gamma> = \<Gamma>" by (meson disjoint_iff fresh_def fresh_star_def supp_perm_eq_test) 

  from 1(1,2,5) g have t1: "set (?tys2 @ ?vals2) \<sharp>* \<tau>" using fresh_in_context_ty[OF 1(8)] unfolding fresh_star_def by auto
  have t2: "set (?tys @ ?vals) \<sharp>* \<tau>" using fresh(3) unfolding fresh_star_def by auto
  then have "supp \<tau> \<inter> supp p = {}" using t1 P(3) unfolding fresh_star_def fresh_def by blast
  then have 4: "p \<bullet> \<tau> = \<tau>" by (meson disjoint_iff fresh_def fresh_star_def supp_perm_eq_test) 

  have "supp cty = {}" using supp_cty[OF valid_axioms] 1(2,9) by simp
  then have 5: "supp args \<subseteq> supp \<sigma>s" using supp_subst_ctor 1(11) by blast

  have "supp args \<subseteq> supp \<Gamma>" using supp_args[OF 1(6,7,9,11)] 1(1) by argo
  then have "supp args \<inter> supp p = {}" using G by blast
  then have 6: "p \<bullet> args = args" by (meson disjoint_iff fresh_def fresh_star_def supp_perm_eq)
  have 7: "p \<bullet> vals2 = vals" "p \<bullet> tys2 = tys" using permute_atoms_split[OF P(2)] by auto

  have "p \<bullet> (zip_with BVar vals2 args @ zip_with BTyVar tys2 ks @ \<Gamma>) , p \<bullet> \<Delta> \<turnstile> e' : p \<bullet> \<tau>" using 1(1,2,5,14) P(1) Tm.eqvt by blast
  then have "zip_with BVar (p \<bullet> vals2) args @ zip_with BTyVar (p \<bullet> tys2) ks @ \<Gamma> , \<Delta> \<turnstile> e' : \<tau>" using 3 4 permute_axioms[OF valid_axioms] 6 by simp
  then have "zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma> , \<Delta> \<turnstile> e' : \<tau>" using 7 by simp
  then show ?thesis using 1 that permute_length[OF 7(1)] permute_length[OF 7(2)] by auto
qed

corollary supp_in_context_term_type: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> supp \<tau> \<subseteq> supp \<Gamma>"
  using typing_regularity supp_in_context_ty by blast

lemma supp_in_context_term_aux:
  shows "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<longrightarrow> supp e \<subseteq> supp \<Gamma>"
  and "\<forall>e. Alts \<Gamma> \<Delta> e alts \<tau> \<longrightarrow> supp alts \<subseteq> supp \<Gamma>"
  and "\<forall>e. Alt \<Gamma> \<Delta> e alt \<tau> \<longrightarrow> supp alt \<subseteq> supp \<Gamma>"
proof (nominal_induct e and alts and alt avoiding: \<Gamma> \<Delta> \<tau> rule: term_alt_list_alt.strong_induct)
  case (Var x)
  then show ?case by (metis TmE(1) fresh_def fresh_not_isin_var singletonD subsetCI supp_at_base term_alt_list_alt.supp(1))
next
  case (App e1 e2)
  then show ?case by (metis TmE(2) Un_least term_alt_list_alt.supp(2))
next
  case (TApp e \<sigma>)
  then show ?case by (metis TmE(3) Un_least supp_in_context_ty term_alt_list_alt.supp(3))
next
  case (Ctor T)
  then show ?case using term_alt_list_alt.supp(4) pure_supp by auto
next
  case (Lam x \<tau>1 e)
  show ?case
  proof standard
    assume a: "\<Gamma> , \<Delta> \<turnstile> \<lambda> x : \<tau>1 . e : \<tau>"
    then have "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (meson CtxE(2) Lam.hyps(1) T_Abs_Inv context_valid_tm) 
    then have 1: "supp \<tau>1 \<subseteq> supp \<Gamma>" by (rule supp_in_context_ty)
    have "supp e \<subseteq> supp (BVar x \<tau>1 # \<Gamma>)" using Lam(4) T_Abs_Inv[OF a Lam(1)] by metis
    then show "supp (\<lambda> x : \<tau>1 . e) \<subseteq> supp \<Gamma>" unfolding term_alt_list_alt.supp supp_Cons binder.supp supp_at_base using 1 by auto
  qed
next
  case (TyLam a k e)
  show ?case
  proof standard
    assume a: "\<Gamma> , \<Delta> \<turnstile> \<Lambda> a : k . e : \<tau>"
    have "supp e \<subseteq> supp (BTyVar a k # \<Gamma>)" using TyLam(4) T_AbsT_Inv[OF a TyLam(1,3)] by metis
    then show "supp (\<Lambda> a : k . e) \<subseteq> supp \<Gamma>" unfolding term_alt_list_alt.supp pure_supp supp_Cons binder.supp supp_at_base by auto
  qed
next
  case (Let x \<tau>1 e1 e2)
  show ?case
  proof standard
    assume a: "\<Gamma> , \<Delta> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>"
    then have "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using Let(1) T_Let_Inv typing_regularity by blast
    then have 1: "supp \<tau>1 \<subseteq> supp \<Gamma>" by (rule supp_in_context_ty)
    have "supp e1 \<subseteq> supp \<Gamma>" "supp e2 \<subseteq> supp (BVar x \<tau>1 # \<Gamma>)" using Let(4,5) T_Let_Inv[OF a Let(1)] by blast+
    then show "supp (Let x \<tau>1 e1 e2) \<subseteq> supp \<Gamma>" unfolding term_alt_list_alt.supp supp_Cons binder.supp supp_at_base using 1 by auto
  qed
next
  case (Case e alts)
  then show ?case unfolding term_alt_list_alt.supp by blast
next
  case ANil
  then show ?case using term_alt_list_alt.supp by simp
next
  case (ACons alt alts)
  then show ?case unfolding term_alt_list_alt.supp by blast
next
  case (MatchCtor K tys vals e')
  show ?case
  proof (standard, standard)
    fix e
    assume a: "Alt \<Gamma> \<Delta> e (MatchCtor K tys vals e') \<tau>"
    obtain \<tau>1 T \<sigma>s cty ks args where P: "\<Gamma> , \<Delta> \<turnstile> e : \<tau>1" "head_data \<tau>1 = Some (T, \<sigma>s)" "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" "AxCtor K cty \<in> set \<Delta>" "ctor_type cty = Some (T, ks)"
      "length args = length vals" "length ks = length tys" "subst_ctor cty \<sigma>s = Some args" "zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma> , \<Delta> \<turnstile> e' : \<tau>"
      by (rule Alt_Ctor_Inv[OF a MatchCtor(1,4,3)])
    then have "supp e' \<subseteq> supp (zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma>)" using MatchCtor(7) by simp
    then have "supp e' \<subseteq> supp vals \<union> supp args \<union> supp tys \<union> supp \<Gamma>" unfolding supp_append using supp_zip_with pure_supp by blast
    then have "supp e' \<subseteq> supp vals \<union> supp tys \<union> supp \<Gamma>" using supp_args[OF P(1,2,4,8)] by blast
    then show "supp (MatchCtor K tys vals e') \<subseteq> supp \<Gamma>" unfolding term_alt_list_alt.supp pure_supp supp_vars supp_tyvars by auto
  qed
qed
corollary supp_in_context_term: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> supp e \<union> supp \<tau> \<subseteq> supp \<Gamma>"
  using supp_in_context_ty[OF typing_regularity] supp_in_context_term_aux(1) by simp
lemmas supp_in_context = supp_in_context_ty supp_in_context_term

corollary fresh_in_context_term_var: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; atom (y::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom y \<sharp> e"
  using supp_in_context_term unfolding fresh_def by blast
corollary fresh_in_context_term_tyvar: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e \<and> atom a \<sharp> \<tau>"
  using supp_in_context_term unfolding fresh_def by blast
lemmas fresh_in_context = fresh_in_context_ty fresh_in_context_term_var fresh_in_context_term_tyvar

nominal_inductive Tm avoids
  Tm_Abs: x
  | Tm_TAbs: a
  | Tm_Let: x
  | Alt_Ctor: tys and vals
proof goal_cases
  case (1 x \<tau>1 \<Gamma> \<Delta> e \<tau>2)
  then have "\<Delta> \<turnstile> BVar x \<tau>1 # \<Gamma>" by (rule context_valid)
  then have 2: "atom x \<sharp> \<Gamma>" by blast
  obtain y e' where 4: "(\<lambda> x:\<tau>1. e) = (\<lambda> y:\<tau>1. e') \<and> atom x \<sharp> (\<lambda> y:\<tau>1. e')" using Abs_fresh_var by auto
  then have "atom x \<sharp> (\<Gamma>, \<Delta>, \<lambda> y:\<tau>1. e', \<tau>1 \<rightarrow> \<tau>2)" using 2 fresh_Pair by simp
  then show ?case using 4 fresh_star_def by fastforce
next
  case (3 a k \<Gamma> \<Delta> e \<sigma>)
  then have "\<Delta> \<turnstile> BTyVar a k # \<Gamma>" by (rule context_valid)
  then have 1: "atom a \<sharp> \<Gamma>" by blast
  have 2: "atom a \<sharp> \<Delta>" by (rule fresh_in_axioms[OF axioms_valid(3)[OF 3]])
  obtain y e' where 3: "(\<Lambda> a:k. e) = (\<Lambda> y:k. e') \<and> atom a \<sharp> (\<Lambda> y:k. e')" using Abs_fresh_var by auto
  obtain y2 \<sigma>' where 4: "(\<forall> a:k. \<sigma>) = (\<forall> y2:k. \<sigma>') \<and> atom a \<sharp> (\<forall> y2:k. \<sigma>')" using Abs_fresh_var by auto
  then have "atom a \<sharp> (\<Gamma>, \<Delta>, \<Lambda> y:k. e', \<forall> y2:k. \<sigma>')" using 1 2 3 by auto
  then show ?case using 3 4 fresh_star_def by force
next
  case (5 \<Gamma> \<Delta> e1 \<tau>1 x e2 \<tau>2)
  from 5(2) have "\<Delta> \<turnstile> BVar x \<tau>1 # \<Gamma>" by (rule context_valid)
  then have 1: "atom x \<sharp> \<Gamma>" by blast
  then have "atom x \<sharp> e1" using 5(1) fresh_in_context(2) by blast
  then obtain y e2' where 2: "Let x \<tau>1 e1 e2 = Let y \<tau>1 e1 e2' \<and> atom x \<sharp> Let y \<tau>1 e1 e2'" using Abs_fresh_var by auto
  then have "atom x \<sharp> (\<Gamma>, \<Delta>, Let y \<tau>1 e1 e2', \<tau>2)" using 1 fresh_Pair by simp
  then show ?case using 2 fresh_star_def by fastforce
next
  case (7 \<Gamma> \<Delta> e \<tau>1 T \<sigma>s \<tau> K cty ks args vals tys e')
  have 1: "\<Delta> \<turnstile> zip_with BVar vals args @ zip_with BTyVar tys ks @ \<Gamma>" by (rule context_valid(2)[OF 7(9)])
  have g1: "set (map atom vals) \<sharp>* \<Gamma>" using zip_with_context_fresh_vars[OF 1] 7(7) unfolding fresh_star_def fresh_append by simp
  have "set (map atom tys) \<sharp>* \<Gamma>" using zip_with_context_fresh_tyvars[OF context_valid_append[OF 1]] 7(8) by simp
  then have 2: "(set (map atom vals) \<union> set (map atom tys)) \<sharp>* \<Gamma>" (is "?x \<sharp>* \<Gamma>") using g1 unfolding fresh_star_def by blast
  have 3: "?x \<sharp>* e" using fresh_in_context(2,3)[OF 7(1)] 2 unfolding fresh_star_def by auto
  have 4: "?x \<sharp>* \<tau>" using fresh_in_context(1)[OF 7(3)] 2 unfolding fresh_star_def by auto
  have "?x \<sharp>* \<Delta>" using fresh_in_axioms[OF axioms_valid(3)[OF 7(1)]] unfolding fresh_star_def by auto
  then show ?case using 2 3 4 unfolding fresh_star_def fresh_Pair by auto
qed auto

end
