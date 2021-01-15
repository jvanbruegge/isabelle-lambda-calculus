theory Determinancy
  imports Typing Typing_Lemmas
begin

lemma unique_ty: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k1 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<rbrakk> \<Longrightarrow> k1 = k2"
proof (nominal_induct \<tau> arbitrary: k1 k2 rule: \<tau>.strong_induct)
  case (TyVar x)
  then show ?case using isin_split isin_same(1) by blast
next
  case (TyConApp \<tau>1 \<tau>2)
  then show ?case by fastforce
next
  case (TyForall x1 x2a x3)
  then show ?case by (metis Ty_Forall_Inv_2)
qed auto

lemma unique_tm: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 ; \<Gamma> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<tau>1 = \<tau>2"
proof (nominal_induct e avoiding: \<Gamma> \<tau>1 \<tau>2 rule: term.strong_induct)
  case (Var x)
  then show ?case using isin_split isin_same(2) by blast
next
  case (TyApp e1 \<tau>)
  obtain a1 k1 \<sigma>1 where 1: "\<Gamma> \<turnstile> e1 : \<forall> a1:k1. \<sigma>1" "\<tau>1 = \<sigma>1[\<tau>/a1]" by (cases rule: Tm.cases[OF TyApp(2)]) auto
  obtain a2 k2 \<sigma>2 where 2: "\<Gamma> \<turnstile> e1 : \<forall> a2:k2. \<sigma>2" "\<tau>2 = \<sigma>2[\<tau>/a2]" by (cases rule: Tm.cases[OF TyApp(3)]) auto
  show ?case using TyApp(1)[OF 1(1) 2(1)] subst_type_same 1(2) 2(2) by simp
next
  case (Lam x \<tau> e)
  then show ?case by (metis T_Abs_Inv)
next
  case (TyLam a k e)
  then show ?case by (metis T_AbsT_Inv)
next
  case (Let x \<tau> e1 e2)
  then show ?case using T_Let_Inv by blast
qed fastforce+

end
