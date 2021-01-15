theory Typing
  imports Syntax Defs Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

inductive Ctx :: "\<Gamma> \<Rightarrow> bool" ("\<turnstile> _")
  and Ty :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _ : _") where

  Ctx_Empty: "\<turnstile> []"

| Ctx_TyVar: "\<lbrakk> \<turnstile> \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> BTyVar a k # \<Gamma>"

| Ctx_Var: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> BVar x \<tau> # \<Gamma>"

(* ------------------------------ *)

| Ty_Var: "\<lbrakk> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"

| Ty_App: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyConApp \<tau>1 \<tau>2 : \<kappa>2"

| Ty_Unit: "\<turnstile> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit : \<star>" (* to be replaced with ADTs *)

| Ty_FunArrow: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2) : \<star>" (* also to be a type constant *)

| Ty_Forall: "\<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a : k. \<sigma>) : \<star>"

equivariance Ctx

inductive Tm :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ : _" 50) where
  Tm_Var: "\<lbrakk> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>"

| Tm_Abs: "BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| Tm_App: "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"

| Tm_TAbs: "BTyVar a k # \<Gamma> \<turnstile> e : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> (\<Lambda> a : k . e) : (\<forall> a : k . \<sigma>)"

| Tm_TApp: "\<lbrakk> \<Gamma> \<turnstile> e : \<forall> a:k. \<sigma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyApp e \<tau> : \<sigma>[\<tau>/a]"

| Tm_Unit: "\<turnstile> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Unit : TyUnit" (* to be replaced with ADTs *)

| Tm_Let: "\<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

equivariance Tm

lemmas Ctx_intros = Ctx_Ty.intros(1-3)
lemmas Ty_intros = Ctx_Ty.intros(4-8)

inductive_cases CtxE[elim]:
  "\<turnstile> BTyVar a k # \<Gamma>"
  "\<turnstile> BVar x \<tau> # \<Gamma>"

inductive_cases TyE[elim!]:
  "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"
  "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyConApp \<tau>1 \<tau>2 : \<kappa>2"
  "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit : k"
  "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2) : k"

inductive_cases TmE[elim!]:
  "\<Gamma> \<turnstile> (Var x) : \<tau>"
  "\<Gamma> \<turnstile> App e1 e2 : \<tau>2"
  "\<Gamma> \<turnstile> TyApp e \<tau> : \<sigma>[\<tau>/a]"
  "\<Gamma> \<turnstile> Unit : \<tau>"

(* Split induction principles *)
lemma Ctx_induct[consumes 1, case_names Empty TyVar Var]:
  assumes "\<turnstile> \<Gamma>"
  and Empty: "P []"
  and TyVar: "\<And>\<Gamma> a k. \<lbrakk> \<turnstile> \<Gamma> ; P \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P (BTyVar a k # \<Gamma>)"
  and Var: "\<And>\<Gamma> x \<tau>. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P (BVar x \<tau> # \<Gamma>)"
shows "P \<Gamma>"
  using assms(1) by (induction \<Gamma> rule: Ctx_Ty.inducts(1)) (auto simp: assms)

lemma Ty_induct[consumes 1, case_names Var App Unit FunArrow Forall]:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa>"
  and Var: "\<And>\<Gamma> a k. \<lbrakk> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> (TyVar a) k"
  and App: "\<And>\<Gamma> \<tau>1 \<tau>2 \<kappa>1 \<kappa>2. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; P \<Gamma> \<tau>1 (KArrow \<kappa>1 \<kappa>2) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; P \<Gamma> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> P \<Gamma> (TyConApp \<tau>1 \<tau>2) \<kappa>2"
  and Unit: "\<And>\<Gamma>. \<turnstile> \<Gamma> \<Longrightarrow> P \<Gamma> TyUnit \<star>"
  and FunArrow: "\<And>\<Gamma> \<tau>1 \<tau>2. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; P \<Gamma> \<tau>1 \<star> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> ; P \<Gamma> \<tau>2 \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> (\<tau>1 \<rightarrow> \<tau>2) \<star>"
  and Forall: "\<And>\<Gamma> a k \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; P (BTyVar a k # \<Gamma>) \<sigma> \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> (\<forall> a:k. \<sigma>) \<star>"
shows "P \<Gamma> \<tau> \<kappa>"
  using assms(1) by (induction \<Gamma> \<tau> \<kappa> rule: Ctx_Ty.inducts(2)) (auto simp: assms)

lemma Ctx_Ty_induct_split[case_names Ctx_Empty Ctx_TyVar Ctx_Var Ty_Var Ty_App Ty_Unit Ty_FunArrow Ty_Forall]:
  assumes "P []"
  and "\<And>\<Gamma>' b k2. \<lbrakk> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Gamma>' ; atom b \<sharp> \<Gamma>' @  \<Gamma> \<rbrakk> \<Longrightarrow> P (BTyVar b k2 # \<Gamma>')"
  and "\<And>\<Gamma>' \<tau> x. \<lbrakk> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; Q \<Gamma>' \<tau> \<star> ; atom x \<sharp> \<Gamma>' @  \<Gamma> \<rbrakk> \<Longrightarrow> P (BVar x \<tau> # \<Gamma>')"
  and "\<And>\<Gamma>' b k2. \<lbrakk> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Gamma>' ; BTyVar b k2 \<in> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> Q \<Gamma>' (TyVar b) k2"
  and "\<And>\<Gamma>' \<tau>1 \<kappa>1 \<kappa>2 \<tau>2. \<lbrakk> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; Q \<Gamma>' \<tau>1 (KArrow \<kappa>1 \<kappa>2) ; \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; Q \<Gamma>' \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> Q \<Gamma>' (TyConApp \<tau>1 \<tau>2) \<kappa>2"
  and "\<And>\<Gamma>'. \<lbrakk> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Gamma>' \<rbrakk> \<Longrightarrow> Q \<Gamma>' TyUnit \<star>"
  and "\<And>\<Gamma>' \<tau>1 \<tau>2. \<lbrakk> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; Q \<Gamma>' \<tau>1 \<star> ; \<Gamma>' @  \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> ; Q \<Gamma>' \<tau>2 \<star> \<rbrakk> \<Longrightarrow> Q \<Gamma>' (\<tau>1 \<rightarrow> \<tau>2) \<star>"
  and "\<And>b k2 \<Gamma>' \<sigma>. \<lbrakk> BTyVar b k2 # \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; Q (BTyVar b k2 # \<Gamma>') \<sigma> \<star> \<rbrakk> \<Longrightarrow> Q \<Gamma>' (\<forall> b : k2 . \<sigma>) \<star>"
shows "\<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Gamma>'"
  and "\<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<tau> k2"
proof -
  let ?\<Gamma> = "\<Gamma>' @ \<Gamma>"
  let ?P = "\<lambda>x. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma>) \<longrightarrow> (P \<Gamma>2)"
  let ?Q = "\<lambda>x y z. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma>) \<longrightarrow> (Q \<Gamma>2 y z)"

  have "(\<turnstile> ?\<Gamma> \<longrightarrow> ?P ?\<Gamma>) \<and> (?\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> ?Q ?\<Gamma> \<tau> k2)"
    apply (cases rule: Ctx_Ty.induct[of "?P" "?Q"]) apply auto
  proof (cases)
    fix \<Gamma>2' b \<kappa> \<Gamma>2
    assume a: "\<turnstile> \<Gamma>2'" "\<forall>\<Gamma>2. \<Gamma>2' = \<Gamma>2 @ \<Gamma> \<longrightarrow> P \<Gamma>2" "atom b \<sharp> \<Gamma>2'" "BTyVar b \<kappa> # \<Gamma>2' = \<Gamma>2 @ \<Gamma>"
    show "P \<Gamma>2"
    proof (cases "\<Gamma>2 = []")
      case False
      then obtain G where "\<Gamma>2' = G @ \<Gamma>" by (meson Cons_eq_append_conv a(4))
      then show ?thesis using assms(2) a by auto
    qed (simp add: assms(1))
  next
    fix \<Gamma>2' \<tau>2 x \<Gamma>2
    assume a: "\<Gamma>2' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" "\<forall>\<Gamma>2. \<Gamma>2' = \<Gamma>2 @ \<Gamma> \<longrightarrow> Q \<Gamma>2 \<tau>2 \<star>" "atom x \<sharp> \<Gamma>2'" "BVar x \<tau>2 # \<Gamma>2' = \<Gamma>2 @ \<Gamma>"
    show "P \<Gamma>2"
    proof (cases "\<Gamma>2 = []")
      case False
      then obtain G where "\<Gamma>2' = G @ \<Gamma>" by (meson Cons_eq_append_conv a(4))
      then show ?thesis using assms(3) a by auto
    qed (simp add: assms(1))
  qed (auto simp: assms(1,4-8))
  then show "\<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Gamma>'" and "\<Gamma>' @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<tau> k2" by simp_all
qed

(* context validity *)
lemma context_valid_ty: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa> \<Longrightarrow> \<turnstile> \<Gamma>"
  by (induction \<Gamma> \<tau> \<kappa> rule: Ty_induct) auto
lemma context_valid_tm: "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> \<turnstile> \<Gamma>"
  by (induction \<Gamma> e \<tau> rule: Tm.induct) (auto simp: context_valid_ty)
lemmas context_valid = context_valid_ty context_valid_tm

(* \<lbrakk> \<Gamma> \<turnstile> e : t ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e *)
lemma fresh_in_context_ty: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (induction \<Gamma> \<tau> k rule: Ty_induct)
  case (Var \<Gamma> a k)
  then show ?case using fresh_at_base(2) fresh_not_isin_tyvar by fastforce
qed (auto simp: fresh_Cons)

lemma fresh_in_context_term_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (induction \<Gamma> e \<tau> rule: Tm.induct)
case (Tm_Var \<Gamma> x \<tau>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_var by force
qed (auto simp: fresh_Cons)

lemma fresh_in_context_term_tyvar: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e"
proof (induction \<Gamma> e \<tau> rule: Tm.induct)
  case (Tm_Abs \<Gamma> x \<tau>1 e \<tau>2)
  then show ?case using Tm_Abs context_valid_tm fresh_Cons fresh_in_context_ty by fastforce
next
  case (Tm_Let \<Gamma> e1 e2 \<tau>1 \<tau>2 x)
  then show ?case
    by (metis (mono_tags, lifting) CtxE(2) binder.fresh(1) context_valid_tm fresh_Cons fresh_in_context_ty fresh_ineq_at_base list.set_intros(1) term.fresh(7))
qed (auto simp: fresh_Cons fresh_in_context_ty)
lemmas fresh_in_context = fresh_in_context_ty fresh_in_context_term_var fresh_in_context_term_tyvar

nominal_inductive Ctx avoids
  Ty_Forall: a
proof (goal_cases)
  case (1 a k \<Gamma> \<sigma>)
  then have "\<turnstile> BTyVar a k # \<Gamma>" by (rule context_valid(1))
  then have 1: "atom a \<sharp> \<Gamma>" by blast
  obtain c \<sigma>' where 2: "(\<forall> a:k. \<sigma>) = (\<forall> c:k. \<sigma>') \<and> atom a \<sharp> (\<forall> c:k. \<sigma>')" using Abs_fresh_var by auto
  then have "atom a \<sharp> (\<Gamma>, \<forall> c:k. \<sigma>', \<star>)" using 1 fresh_Pair by simp
  then show ?case using 2 fresh_star_def by fastforce
qed auto

nominal_inductive Tm avoids
  Tm_Abs: x
  | Tm_TAbs: a
  | Tm_Let: x
proof (goal_cases)
  case (1 x \<tau>1 \<Gamma> e \<tau>2)
  then have "\<turnstile> BVar x \<tau>1 # \<Gamma>" by (rule context_valid)
  then have 1: "atom x \<sharp> \<Gamma>" by blast
  obtain y e' where 2: "(\<lambda> x:\<tau>1. e) = (\<lambda> y:\<tau>1. e') \<and> atom x \<sharp> (\<lambda> y:\<tau>1. e')" using Abs_fresh_var by auto
  then have "atom x \<sharp> (\<Gamma>, \<lambda> y:\<tau>1. e', \<tau>1 \<rightarrow> \<tau>2)" using 1 fresh_Pair by simp
  then show ?case using 2 fresh_star_def by fastforce
next
  case (3 a k \<Gamma> e \<sigma>)
  then have "\<turnstile> BTyVar a k # \<Gamma>" by (rule context_valid)
  then have 1: "atom a \<sharp> \<Gamma>" by blast
  obtain y e' where 2: "(\<Lambda> a:k. e) = (\<Lambda> y:k. e') \<and> atom a \<sharp> (\<Lambda> y:k. e')" using Abs_fresh_var by auto
  obtain y2 \<sigma>' where 3: "(\<forall> a:k. \<sigma>) = (\<forall> y2:k. \<sigma>') \<and> atom a \<sharp> (\<forall> y2:k. \<sigma>')" using Abs_fresh_var by auto
  then have "atom a \<sharp> (\<Gamma>, \<Lambda> y:k. e', \<forall> y2:k. \<sigma>')" using 1 2 by auto
  then show ?case using 2 3 fresh_star_def by force
next
  case (5 \<Gamma> e1 \<tau>1 x e2 \<tau>2)
  from 5(2) have "\<turnstile> BVar x \<tau>1 # \<Gamma>" by (rule context_valid)
  then have 1: "atom x \<sharp> \<Gamma>" by blast
  then have "atom x \<sharp> e1" using 5(1) fresh_in_context(2) by blast
  then obtain y e2' where 2: "Let x \<tau>1 e1 e2 = Let y \<tau>1 e1 e2' \<and> atom x \<sharp> Let y \<tau>1 e1 e2'" using Abs_fresh_var by auto
  then have "atom x \<sharp> (\<Gamma>, Let y \<tau>1 e1 e2', \<tau>2)" using 1 fresh_Pair by simp
  then show ?case using 2 fresh_star_def by fastforce
qed auto

(* Split strong induction principles *)
lemma Ctx_strong_induct[consumes 1, case_names Empty TyVar Var]:
  fixes c::"'a::fs"
  assumes "\<turnstile> \<Gamma>"
  and Empty: "\<And>c. P c []"
  and TyVar: "\<And>\<Gamma> a k c. \<lbrakk> \<turnstile> \<Gamma> ; (\<And>c. P c \<Gamma>) ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P c (BTyVar a k # \<Gamma>)"
  and Var: "\<And>\<Gamma> x \<tau> c. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P c (BVar x \<tau> # \<Gamma>)"
shows "P c \<Gamma>"
  using assms(1) by (induction \<Gamma> rule: Ctx_Ty.strong_induct(1)[of _ P "\<lambda>c \<Gamma> \<tau> k. True"]) (auto simp: assms)

lemma Ty_strong_induct[consumes 1, case_names Var App Unit FunArrow Forall]:
  fixes c::"'a::fs"
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa>"
  and Var: "\<And>\<Gamma> a k c. \<lbrakk> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P c \<Gamma> (TyVar a) k"
  and App: "\<And>\<Gamma> \<tau>1 \<kappa>1 \<kappa>2 \<tau>2 c. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow \<kappa>1 \<kappa>2 ; (\<And>c. P c \<Gamma> \<tau>1 (KArrow \<kappa>1 \<kappa>2)) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; (\<And>c. P c \<Gamma> \<tau>2 \<kappa>1) \<rbrakk> \<Longrightarrow> P c \<Gamma> (TyConApp \<tau>1 \<tau>2) \<kappa>2"
  and Unit: "\<And>\<Gamma> c. \<turnstile> \<Gamma> \<Longrightarrow> P c \<Gamma> TyUnit \<star>"
  and FunArrow: "\<And>\<Gamma> \<tau>1 \<tau>2 c. \<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> ; (\<And>c. P c \<Gamma> \<tau>1 \<star>) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star> ; (\<And>c. P c \<Gamma> \<tau>2 \<star>) \<rbrakk> \<Longrightarrow> P c \<Gamma> (\<tau>1 \<rightarrow> \<tau>2) \<star>"
  and Forall: "\<And>a k \<Gamma> \<sigma> c. \<lbrakk> atom a \<sharp> c ; BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; (\<And>c. P c (BTyVar a k # \<Gamma>) \<sigma> \<star>) \<rbrakk> \<Longrightarrow> P c \<Gamma> (\<forall> a : k . \<sigma>) \<star>"
shows "P c \<Gamma> \<tau> \<kappa>"
  using assms(1) by (induction \<Gamma> \<tau> \<kappa> rule: Ctx_Ty.strong_induct(2)[of _ _ _ "\<lambda>c xs. True" P]) (auto simp: assms fresh_star_def)

end
