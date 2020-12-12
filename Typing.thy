theory Typing
  imports Syntax Defs
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

inductive Ctx :: "\<Gamma> \<Rightarrow> bool" ("\<turnstile> _")
  and Ty :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _")
  and Tm :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ : _" 50) where

  Ctx_Empty: "\<turnstile> []"

| Ctx_TyVar: "\<lbrakk> \<turnstile> \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> BTyVar a k # \<Gamma>"

| Ctx_Var: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> BVar x \<tau> # \<Gamma>"

(* ------------------------------ *)

| Ty_Var: "\<lbrakk> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"

| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyConApp \<tau>1 \<tau>2 : \<kappa>2"

| Ty_Unit: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit : \<star>" (* to be replaced with ADTs *)

| Ty_FunArrow: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2) : \<star>" (* also to be a type constant *)

| Ty_Forall: "\<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a : k. \<sigma>) : \<star>"

(* ------------------------------ *)

| Tm_Var: "\<lbrakk> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>"

| Tm_Abs: "BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| Tm_App: "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"

| Tm_TAbs: "BTyVar a k # \<Gamma> \<turnstile> e : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> (\<Lambda> a : k . e) : (\<forall> a : k . \<sigma>)"

| Tm_TApp: "\<lbrakk> \<Gamma> \<turnstile> e : \<forall> a:k. \<sigma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyApp e \<tau> : \<sigma>[\<tau>/a]"

| Tm_Unit: "\<Gamma> \<turnstile> Unit : TyUnit" (* to be replaced with ADTs *)

| Tm_Let: "\<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

equivariance Ctx
nominal_inductive Ctx .

lemma Ctx_induct[consumes 1, case_names Empty TyVar Var]:
  assumes "\<turnstile> \<Gamma>"
  and Empty: "P []"
  and TyVar: "\<And>\<Gamma> a k. \<lbrakk> \<turnstile> \<Gamma> ; P \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P (BTyVar a k # \<Gamma>)"
  and Var: "\<And>\<Gamma> x \<tau>. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P (BVar x \<tau> # \<Gamma>)"
shows "P \<Gamma>"
  using assms(1) by (induction \<Gamma> rule: Ctx_Ty_Tm.inducts(1)) (auto simp: assms)

lemma Ty_induct[consumes 1, case_names Var App Unit FunArrow Forall]:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa>"
  and Var: "\<And>\<Gamma> a k. \<lbrakk> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> (TyVar a) k"
  and App: "\<And>\<Gamma> \<tau>1 \<tau>2 \<kappa>1 \<kappa>2. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; P \<Gamma> \<tau>1 (KArrow \<kappa>1 \<kappa>2) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; P \<Gamma> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> P \<Gamma> (TyConApp \<tau>1 \<tau>2) \<kappa>2"
  and Unit: "\<And>\<Gamma>. P \<Gamma> TyUnit \<star>"
  and FunArrow: "\<And>\<Gamma> \<tau>1 \<tau>2. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; P \<Gamma> \<tau>1 \<star> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> ; P \<Gamma> \<tau>2 \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> (\<tau>1 \<rightarrow> \<tau>2) \<star>"
  and Forall: "\<And>\<Gamma> a k \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; P (BTyVar a k # \<Gamma>) \<sigma> \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> (\<forall> a:k. \<sigma>) \<star>"
shows "P \<Gamma> \<tau> \<kappa>"
  using assms(1) by (induction \<Gamma> \<tau> \<kappa> rule: Ctx_Ty_Tm.inducts(2)) (auto simp: assms)

lemma Tm_induct[consumes 1, case_names Var Abs App TAbs TApp Unit Let]:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  and Var: "\<And>\<Gamma> x \<tau>. \<lbrakk> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> (Var x) \<tau>"
  and Abs: "\<And>\<Gamma> x \<tau>1 e \<tau>2. \<lbrakk> BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 ; P (BVar x \<tau>1 # \<Gamma>) e \<tau>2 \<rbrakk> \<Longrightarrow> P \<Gamma> (\<lambda> x:\<tau>1. e) (\<tau>1 \<rightarrow> \<tau>2)"
  and App: "\<And>\<Gamma> e1 e2 \<tau>1 \<tau>2. \<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; P \<Gamma> e1 (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 ; P \<Gamma> e2 \<tau>1 \<rbrakk> \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>2"
  and TAbs: "\<And>\<Gamma> a k e \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> \<turnstile> e : \<sigma> ; P (BTyVar a k # \<Gamma>) e \<sigma> \<rbrakk> \<Longrightarrow> P \<Gamma> (\<Lambda> a:k. e) (\<forall> a:k. \<sigma>)"
  and TApp: "\<And>\<Gamma> a k e \<sigma> \<tau>. \<lbrakk> \<Gamma> \<turnstile> e : (\<forall> a:k. \<sigma>) ; P \<Gamma> e (\<forall> a:k. \<sigma>) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> P \<Gamma> (TyApp e \<tau>) \<sigma>[\<tau>/a]"
  and Unit: "\<And>\<Gamma>. P \<Gamma> Unit TyUnit"
  and Let: "\<And>\<Gamma> e1 e2 \<tau>1 \<tau>2 x. \<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>1 ; P \<Gamma> e1 \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 ; P (BVar x \<tau>1 # \<Gamma>) e2 \<tau>2 \<rbrakk> \<Longrightarrow> P \<Gamma> (Let x \<tau>1 e1 e2) \<tau>2"
shows "P \<Gamma> e \<tau>"
  using assms(1) by (induction \<Gamma> e \<tau> rule: Ctx_Ty_Tm.inducts(3)) (auto simp: assms)

end
