theory Typing
  imports Syntax Defs
begin

inductive Ty :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _") where
  Ty_Unit: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit : \<star>"

| Ty_Var: "BTyVar a k \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"

| Ty_Arrow: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2) : \<star>"

| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyConApp \<tau>1 \<tau>2 : \<kappa>2"

| Ty_Forall: "\<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a : k. \<sigma>) : \<star>"
equivariance Ty
nominal_inductive Ty avoids
  Ty_Forall: a
  by (auto simp: fresh_star_def)

inductive T :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ : _" 50) where
  T_UnitI: "(\<Gamma> \<turnstile> Unit : TyUnit)"

| T_VarI: "\<lbrakk> BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>"

| T_AbsI: "\<lbrakk> atom x \<sharp> \<Gamma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| T_AppI: "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"

| T_LetI: "\<lbrakk> atom x \<sharp> (\<Gamma>, e1) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 ; \<Gamma> \<turnstile> e1 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

| T_AppTI: "\<lbrakk> \<Gamma> \<turnstile> e : (\<forall>a : k . \<sigma>) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyApp e \<tau> : subst_type \<tau> a \<sigma>"

| T_AbsTI: "\<lbrakk> BTyVar a k # \<Gamma> \<turnstile> e : \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<Lambda> a : k . e) : (\<forall> a : k . \<sigma>)"
equivariance T
nominal_inductive T avoids
  T_AbsI: x
  | T_LetI: x
  | T_AbsTI: a
  by (auto simp: fresh_star_def fresh_Unit fresh_Pair)

end
