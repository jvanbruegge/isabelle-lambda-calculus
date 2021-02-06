theory Typing
  imports Syntax Defs Lemmas "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

inductive Ax :: "\<Delta> \<Rightarrow> bool" ("\<turnstile> _")
  and Ctx :: "\<Delta> \<Rightarrow> \<Gamma> \<Rightarrow> bool" ("_ \<turnstile> _")
  and Ty :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool" ("_ , _ \<turnstile>\<^sub>t\<^sub>y _ : _") where

  Ax_Empty: "\<turnstile> []"

| Ax_Data: "\<lbrakk> \<turnstile> \<Delta> ; atom T \<sharp> \<Delta> \<rbrakk> \<Longrightarrow> \<turnstile> AxData T \<kappa> # \<Delta>"

| Ax_Ctor: "\<lbrakk> [] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom D \<sharp> \<Delta> \<rbrakk> \<Longrightarrow> \<turnstile> AxCtor D \<tau> # \<Delta>"

(* ------------------------------ *)

| Ctx_Empty: "\<turnstile> \<Delta> \<Longrightarrow> \<Delta> \<turnstile> []"

| Ctx_TyVar: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> BTyVar a k # \<Gamma>"

| Ctx_Var: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> BVar x \<tau> # \<Gamma>"

(* ------------------------------ *)

| Ty_Var: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"

| Ty_App: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyApp \<tau>1 \<tau>2 : \<kappa>2"

| Ty_Data: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T TNil : k"

| Ty_DataApp: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k1 \<rightarrow> k2 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T (TCons \<tau>2 tys) : k2"

| Ty_Arrow: "\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyArrow : \<star> \<rightarrow> \<star> \<rightarrow> \<star>"

| Ty_Forall: "\<lbrakk> BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (\<forall>a : k. \<sigma>) : \<star>"

method solve_Ax_Ctx_Ty = (
  rule Ty_Arrow
  | match conclusion in
    "\<turnstile> []" \<Rightarrow> \<open>rule Ax_Empty\<close>
    \<bar> "\<turnstile> AxData _ _ # _" \<Rightarrow> \<open>rule Ax_Data\<close>
    \<bar> "\<turnstile> AxCtor _ _ # _" \<Rightarrow> \<open>rule Ax_Ctor\<close>
    \<bar> "_ \<turnstile> BTyVar _ _ # _" \<Rightarrow> \<open>rule Ctx_TyVar\<close>
    \<bar> "(_::\<Delta>) \<turnstile> []" \<Rightarrow> \<open>rule Ctx_Empty\<close>
    \<bar> "_ , _ \<turnstile>\<^sub>t\<^sub>y TyForall _ _ _ : _" \<Rightarrow> \<open>rule Ty_Forall\<close>
    \<bar> "_ , _ \<turnstile>\<^sub>t\<^sub>y TyData _ (TCons _ _) : _" \<Rightarrow> \<open>rule Ty_DataApp\<close>
    \<bar> "_ , _ \<turnstile>\<^sub>t\<^sub>y TyData _ TNil : _" \<Rightarrow> \<open>rule Ty_Data\<close>
    \<bar> "_ , _ \<turnstile>\<^sub>t\<^sub>y TyApp _ _ : _" \<Rightarrow> \<open>rule Ty_App\<close>
    \<bar> "_ , _ \<turnstile>\<^sub>t\<^sub>y TyVar _ : _" \<Rightarrow> \<open>rule Ty_Var\<close>
    \<bar> "_ \<sharp> []" \<Rightarrow> \<open>rule fresh_Nil\<close>
  | (simp add: fresh_Nil fresh_Cons)
  | (simp add: fresh_at_base Abs_ctor_name_inject Abs_data_name_inject)
)+

abbreviation mkCtor :: "nat \<Rightarrow> ctor_name" where
  "mkCtor n \<equiv> Abs_ctor_name (Atom (Sort ''Syntax.ctor_name'' []) n)"

abbreviation mkData :: "nat \<Rightarrow> data_name" where
  "mkData n \<equiv> Abs_data_name (Atom (Sort ''Syntax.data_name'' []) n)"

(* data Maybe a = Nothing | Just a ; data Bool = True | False *)
lemma "\<turnstile> [
  AxCtor (mkCtor 2) (\<forall> a:\<star> . TyVar a \<rightarrow> TyData (mkData 0) (TCons (TyVar a) TNil)),
  AxCtor (mkCtor 4) (TyData (mkData 3) TNil),
  AxCtor (mkCtor 5) (TyData (mkData 3) TNil),
  AxCtor (mkCtor 1) (\<forall> a:\<star> . TyData (mkData 0) (TCons (TyVar a) TNil) ),
  AxData (mkData 3) \<star>,
  AxData (mkData 0) (\<star> \<rightarrow> \<star>)
]" (* 0: Maybe, 1: Nothing, 2: Just, 3: Bool, 4: True, 5: False *)
  by solve_Ax_Ctx_Ty

equivariance Ax

inductive Tm :: "\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ , _ \<turnstile> _ : _" 50) where
  Tm_Var: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BVar x \<tau> \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (Var x) : \<tau>"

| Tm_Abs: "BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2 \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| Tm_App: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> App e1 e2 : \<tau>2"

| Tm_TAbs: "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<sigma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> (\<Lambda> a : k . e) : (\<forall> a : k . \<sigma>)"

| Tm_TApp: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<forall> a:k. \<sigma> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> TApp e \<tau> : \<sigma>[\<tau>/a]"

| Tm_Ctor: "\<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxCtor D \<tau> \<in> set \<Delta> \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Ctor D TNil ENil : \<tau>"

| Tm_CtorApp: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals : \<tau>1 \<rightarrow> \<tau>2 ; \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Ctor D tys (ECons e vals) : \<tau>2"

| Tm_CtorTApp: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> Ctor D tys ENil : \<forall> a:k. \<sigma> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Ctor D (TCons \<tau> tys) ENil : \<sigma>[\<tau>/a]"

| Tm_Let: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 ; BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

equivariance Tm

lemmas Ax_intros = Ax_Ctx_Ty.intros(1-3)
lemmas Ctx_intros = Ax_Ctx_Ty.intros(4-6)
lemmas Ty_intros = Ax_Ctx_Ty.intros(7-12)

inductive_cases AxE[elim]:
  "\<turnstile> AxData T k # \<Delta>"
  "\<turnstile> AxCtor D \<tau> # \<Delta>"

inductive_cases CtxE[elim]:
  "\<Delta> \<turnstile> BTyVar a k # \<Gamma>"
  "\<Delta> \<turnstile> BVar x \<tau> # \<Gamma>"

inductive_cases TyE[elim!]:
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyVar a : k"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyApp \<tau>1 \<tau>2 : \<kappa>2"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData D TNil : k"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData D (TCons \<tau> tys) : k"
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyArrow : k"

inductive_cases TmE[elim!]:
  "\<Gamma> , \<Delta> \<turnstile> (Var x) : \<tau>"
  "\<Gamma> , \<Delta> \<turnstile> App e1 e2 : \<tau>2"
  "\<Gamma> , \<Delta> \<turnstile> TApp e \<tau> : \<tau>2"
  "\<Gamma> , \<Delta> \<turnstile> Ctor D TNil ENil : \<tau>"
  "\<Gamma> , \<Delta> \<turnstile> Ctor D (TCons \<sigma> tys) ENil : \<tau>"
  "\<Gamma> , \<Delta> \<turnstile> Ctor D tys (ECons e vals) : \<tau>"

(* Split induction principles *)
lemma Ax_induct[consumes 1, case_names Empty Data Ctor]:
  assumes "\<turnstile> \<Delta>"
  and "P []"
  and "\<And>T \<Delta> \<kappa>. \<lbrakk> \<turnstile> \<Delta> ; P \<Delta> ; atom T \<sharp> \<Delta> \<rbrakk> \<Longrightarrow> P (AxData T \<kappa> # \<Delta>)"
  and "\<And>\<Delta> \<tau> D. \<lbrakk> [] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom D \<sharp> \<Delta> \<rbrakk> \<Longrightarrow> P (AxCtor D \<tau> # \<Delta>)"
shows "P \<Delta>"
  using Ax_Ctx_Ty.inducts(1)[OF assms(1), of P "\<lambda>a b c d. True" "\<lambda>a b. True"] assms(2-4) by simp

lemma Ctx_induct[consumes 1, case_names Empty TyVar Var]:
  fixes \<Delta>::"\<Delta>"
  assumes "\<Delta> \<turnstile> \<Gamma>"
  and Empty: "\<And>\<Delta>. P \<Delta> []"
  and TyVar: "\<And>\<Delta> \<Gamma> a k. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; P \<Delta> \<Gamma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Delta> (BTyVar a k # \<Gamma>)"
  and Var: "\<And>\<Gamma> \<Delta> x \<tau>. \<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Delta> (BVar x \<tau> # \<Gamma>)"
shows "P \<Delta> \<Gamma>"
  using Ax_Ctx_Ty.inducts(2)[OF assms(1), of "\<lambda>x. True" "\<lambda>a b c d. True" P] assms(2-4) by simp

lemma Ty_induct[consumes 1, case_names Var App Data DataApp Arrow Forall]:
  fixes P::"\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool"
  assumes "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa>"
  and Var: "\<And>\<Gamma> \<Delta> a k. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; BTyVar a k \<in> \<Gamma> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyVar a) k"
  and App: "\<And>\<Gamma> \<Delta> \<tau>1 \<tau>2 \<kappa>1 \<kappa>2. \<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; P \<Gamma> \<Delta> \<tau>1 (KArrow \<kappa>1 \<kappa>2) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; P \<Gamma> \<Delta> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyApp \<tau>1 \<tau>2) \<kappa>2"
  and Data: "\<And>\<Delta> \<Gamma> T k. \<lbrakk> \<Delta> \<turnstile> \<Gamma> ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyData T TNil) k"
  and DataApp: "\<And>\<Gamma> \<Delta> T tys \<tau>2 k1 k2. \<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k1 \<rightarrow> k2 ; P \<Gamma> \<Delta> (TyData T tys) (k1 \<rightarrow> k2) ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1 ; P \<Gamma> \<Delta> \<tau>2 k1 \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (TyData T (TCons \<tau>2 tys)) k2"
  and Arrow: "\<And>\<Gamma> \<Delta>. \<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P \<Gamma> \<Delta> TyArrow (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)"
  and Forall: "\<And>\<Gamma> \<Delta> a k \<sigma>. \<lbrakk> BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; P (BTyVar a k # \<Gamma>) \<Delta> \<sigma> \<star> \<rbrakk> \<Longrightarrow> P \<Gamma> \<Delta> (\<forall> a:k. \<sigma>) \<star>"
shows "P \<Gamma> \<Delta> \<tau> \<kappa>"
  using Ax_Ctx_Ty.inducts(3)[OF assms(1), of "\<lambda>a. True" P "\<lambda>a b. True"] assms(2-7) by simp

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
  by (induction \<Gamma> \<Delta> e \<tau> rule: Tm.induct) (auto simp: axioms_valid_context axioms_valid_ty)
lemmas axioms_valid = axioms_valid_context axioms_valid_ty axioms_valid_tm

lemma Ctx_Ty_induct_split[case_names Ctx_Empty Ctx_TyVar Ctx_Var Ty_Var Ty_App Ty_Data Ty_DataApp Ty_Arrow Ty_Forall]:
  fixes P::"\<Delta> \<Rightarrow> \<Gamma> \<Rightarrow> bool" and Q::"\<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> \<tau> \<Rightarrow> \<kappa> \<Rightarrow> bool"
  assumes "\<And>\<Delta>. \<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P \<Delta> []"
  and "\<And>\<Gamma>' \<Delta> b k2. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; atom b \<sharp> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> P \<Delta> (BTyVar b k2 # \<Gamma>')"
  and "\<And>\<Gamma>' \<Delta> \<tau> x. \<lbrakk> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star> ; Q \<Gamma>' \<Delta> \<tau> \<star> ; atom x \<sharp> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> P \<Delta> (BVar x \<tau> # \<Gamma>')"
  and "\<And>\<Gamma>' \<Delta> b k2. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; BTyVar b k2 \<in> (\<Gamma>' @  \<Gamma>) \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyVar b) k2"
  and "\<And>\<Gamma>' \<Delta> \<tau>1 \<kappa>1 \<kappa>2 \<tau>2. \<lbrakk> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<kappa>1 \<rightarrow> \<kappa>2 ; Q \<Gamma>' \<Delta> \<tau>1 (\<kappa>1 \<rightarrow> \<kappa>2) ; \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<kappa>1 ; Q \<Gamma>' \<Delta> \<tau>2 \<kappa>1 \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyApp \<tau>1 \<tau>2) \<kappa>2"
  and "\<And>\<Gamma>' \<Delta> T k. \<lbrakk> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma> ; P \<Delta> \<Gamma>' ; AxData T k \<in> set \<Delta> \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyData T TNil) k"
  and "\<And>\<Gamma>' \<Delta> T tys \<tau>2 k1 k2. \<lbrakk> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k1 \<rightarrow> k2 ; Q \<Gamma>' \<Delta> (TyData T tys) (k1 \<rightarrow> k2) ; \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1 ; Q \<Gamma>' \<Delta> \<tau>2 k1 \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (TyData T (TCons \<tau>2 tys)) k2"
  and "\<And>\<Gamma>' \<Delta>. \<lbrakk> \<Delta> \<turnstile> (\<Gamma>' @ \<Gamma>) ; P \<Delta> \<Gamma>' \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> TyArrow (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)"
  and "\<And>\<Gamma>' \<Delta> b k2 \<sigma>. \<lbrakk> BTyVar b k2 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> ; Q (BTyVar b k2 # \<Gamma>') \<Delta> \<sigma> \<star> \<rbrakk> \<Longrightarrow> Q \<Gamma>' \<Delta> (\<forall> b : k2 . \<sigma>) \<star>"
shows "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Delta> \<Gamma>'"
  and "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<Delta> \<tau> k2"
proof -
  let ?\<Gamma> = "\<Gamma>' @ \<Gamma>"
  let ?P = "\<lambda>\<Delta> x. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma>) \<longrightarrow> (P \<Delta> \<Gamma>2)"
  let ?Q = "\<lambda>x \<Delta> y z. \<forall>\<Gamma>2. (x = \<Gamma>2 @ \<Gamma>) \<longrightarrow> (Q \<Gamma>2 \<Delta> y z)"

  have "(\<turnstile> \<Delta> \<longrightarrow> True) \<and> (\<Delta> \<turnstile> ?\<Gamma> \<longrightarrow> ?P \<Delta> ?\<Gamma>) \<and> (?\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> ?Q ?\<Gamma> \<Delta> \<tau> k2)"
  proof (cases rule: Ax_Ctx_Ty.induct[of "\<lambda>x. True" "?Q" "?P"])
    case (Ctx_Empty \<Delta>)
    then show ?case
    proof (auto, goal_cases)
      case 1
      then show ?case using assms(1) Ax_Ctx_Ty.Ctx_Empty[OF Ctx_Empty(1)] by simp
    qed
  next
    case (Ctx_TyVar \<Delta> \<Gamma>' a k)
    then show ?case
    proof auto
      fix \<Gamma>2
      assume a: "BTyVar a k # \<Gamma>' = \<Gamma>2 @ \<Gamma>"
      then show "P \<Delta> \<Gamma>2"
      proof (cases "\<Gamma>2 = []")
        case True
        then have "\<Delta> \<turnstile> \<Gamma>" using Ax_Ctx_Ty.Ctx_TyVar[OF Ctx_TyVar(1,3)] a by auto
        then show ?thesis using assms(1) True by simp
      next
        case False
        then obtain G where "\<Gamma>' = G @ \<Gamma>" by (meson Cons_eq_append_conv a)
        then show ?thesis using assms(2) Ctx_TyVar a by auto
      qed
    qed
  next
    case (Ctx_Var \<Gamma>' \<Delta> \<tau> x)
    then show ?case
    proof auto
      fix \<Gamma>2
      assume a: "BVar x \<tau> # \<Gamma>' = \<Gamma>2 @ \<Gamma>"
      then show "P \<Delta> \<Gamma>2"
      proof (cases "\<Gamma>2 = []")
        case True
        then have "\<Delta> \<turnstile> \<Gamma>" using Ax_Ctx_Ty.Ctx_Var[OF Ctx_Var(1,3)] a by simp
        then show ?thesis using True assms(1) by simp
      next
        case False
        then obtain G where "\<Gamma>' = G @ \<Gamma>" by (meson Cons_eq_append_conv a)
        then show ?thesis using assms(3) Ctx_Var a by auto
      qed
    qed
  next
    case (Ty_DataApp \<Gamma>' \<Delta> T tys k1 k2 \<tau>2)
    show ?case
    proof auto
      fix \<Gamma>2
      assume a: "\<Gamma>' = \<Gamma>2 @ \<Gamma>"
      show "Q \<Gamma>2 \<Delta> (TyData T (TCons \<tau>2 tys)) k2" using assms(7) a Ty_DataApp by simp
    qed
  qed (auto simp: assms(1,4-9))

  then show "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma> \<longrightarrow> P \<Delta> \<Gamma>'" and "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> Q \<Gamma>' \<Delta> \<tau> k2" by simp_all
qed

(* context validity *)
lemma context_valid_ty: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<kappa> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
  by (induction \<Gamma> \<Delta> \<tau> \<kappa> rule: Ty_induct) auto
lemma context_valid_tm: "\<Gamma> , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
  by (induction \<Gamma> \<Delta> e \<tau> rule: Tm.induct) (auto simp: context_valid_ty)
lemmas context_valid = context_valid_ty context_valid_tm

(* \<lbrakk> \<Gamma> \<turnstile> e : t ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e *)
lemma fresh_in_context_ty: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (induction \<Gamma> \<Delta> \<tau> k rule: Ty_induct)
  case (Var \<Gamma> \<Delta> a k)
  then show ?case using fresh_at_base(2) fresh_not_isin_tyvar by fastforce
qed (auto simp: fresh_Cons)

lemma fresh_in_context_term_var: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (induction \<Gamma> \<Delta> e \<tau> rule: Tm.induct)
case (Tm_Var \<Gamma> \<Delta> x \<tau>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_var by force
qed (auto simp: fresh_Cons)

lemma fresh_in_context_term_tyvar: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e"
proof (induction \<Gamma> \<Delta> e \<tau> rule: Tm.induct)
  case (Tm_Abs x \<tau>1 \<Gamma> \<Delta> e \<tau>2)
  then have "atom a \<sharp> \<tau>1" by (meson CtxE(2) context_valid_tm fresh_in_context_ty)
  then show ?case by (simp add: Tm_Abs fresh_Cons)
next
  case (Tm_Let \<Gamma> e1 e2 \<tau>1 \<tau>2 x)
  then show ?case
    by (metis (mono_tags, lifting) CtxE(2) binder.fresh(1) context_valid_tm fresh_Cons fresh_in_context_ty fresh_ineq_at_base list.set_intros(1) term_elist.fresh(7))
qed (auto simp: fresh_Cons fresh_in_context_ty)
lemmas fresh_in_context = fresh_in_context_ty fresh_in_context_term_var fresh_in_context_term_tyvar

lemma fresh_in_axioms: "\<turnstile> \<Delta> \<Longrightarrow> atom (a::tyvar) \<sharp> \<Delta>"
proof -
  fix \<Gamma> \<tau> k
  assume a: "\<turnstile> \<Delta>"
  let ?Q = "\<lambda>b c d e. atom a \<sharp> c"
  let ?W = "\<lambda>b c. atom a \<sharp> b"

  have "(\<turnstile> \<Delta> \<longrightarrow> atom a \<sharp> \<Delta>) \<and> (\<Delta> \<turnstile> \<Gamma> \<longrightarrow> ?W \<Delta> \<Gamma>) \<and> (\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k \<longrightarrow> ?Q \<Gamma> \<Delta> \<tau> k)"
  proof (induction rule: Ax_Ctx_Ty.induct[of "\<lambda>x. atom a \<sharp> x" ?Q ?W])
    case (Ax_Ctor \<Delta> \<tau> D)
    then show ?case using fresh_in_context(1)[OF Ax_Ctor(1) fresh_Nil] fresh_Cons fresh_Nil by fastforce
  qed (auto simp: fresh_Nil fresh_Cons)

  then show ?thesis using a by simp
qed

lemma perm_axioms_tyvars[simp]: "\<turnstile> \<Delta> \<Longrightarrow> ((a::tyvar) \<leftrightarrow> b) \<bullet> \<Delta> = \<Delta>"
  using flip_fresh_fresh fresh_in_axioms by blast

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

nominal_inductive Tm avoids
  Tm_Abs: x
  | Tm_TAbs: a
  | Tm_Let: x
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
qed auto

end
