theory Typing
  imports Syntax Defs
begin

inductive Ty :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _") where
  Ty_Unit: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit"

| Ty_Var: "\<lbrakk> BTyVar a \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a"

| Ty_Arrow: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2)"

| Ty_Forall: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a. \<sigma>)"
equivariance Ty
nominal_inductive Ty avoids
  Ty_Forall: a
  by (auto simp: fresh_star_def)

inductive T :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ : _" 50) where
  T_UnitI: "(\<Gamma> \<turnstile> Unit : TyUnit)"

| T_VarI: "\<lbrakk> BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>"

| T_AbsI: "\<lbrakk> atom x \<sharp> \<Gamma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| T_AppI: "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"

| T_LetI: "\<lbrakk> atom x \<sharp> (\<Gamma>, e1) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 ; \<Gamma> \<turnstile> e1 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

| T_AppTI: "\<lbrakk> \<Gamma> \<turnstile> e : (\<forall>a . \<sigma>) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyApp e \<tau> : subst_type \<tau> a \<sigma>"

| T_AbsTI: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile> e : \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<Lambda> a . e) : (\<forall> a . \<sigma>)"
equivariance T
nominal_inductive T avoids
  T_AbsI: x
  | T_LetI: x
  | T_AbsTI: a
  by (auto simp: fresh_star_def fresh_Unit fresh_Pair)

end