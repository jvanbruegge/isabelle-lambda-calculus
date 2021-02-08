theory Determinancy
  imports Typing Typing_Lemmas
begin

lemma unique_ty: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k1 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<rbrakk> \<Longrightarrow> k1 = k2"
proof (nominal_induct \<tau> arbitrary: k1 k2 rule: \<tau>.strong_induct)
  case (TyVar x)
  then show ?case using isin_split isin_same(1) by blast
next
  case (TyData x)
  then show ?case using axiom_isin_split axiom_isin_same(1) axioms_valid(2)[OF TyData(2)] by blast
next
  case (TyApp \<tau>1 \<tau>2)
  then show ?case by fastforce
next
  case (TyForall x1 x2a x3)
  then show ?case by (metis Ty_Forall_Inv_2)
qed auto

lemma unique_tm: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 ; \<Gamma> , \<Delta> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<tau>1 = \<tau>2"
proof (nominal_induct e avoiding: \<Gamma> \<tau>1 \<tau>2 rule: term.strong_induct)
  case (Var x)
  then show ?case using isin_split isin_same(2) by blast
next
  case (App e1 e2)
  then show ?case by fastforce
next
  case (TApp e1 \<tau>)
  obtain a1 k1 \<sigma>1 where 1: "\<Gamma> , \<Delta> \<turnstile> e1 : \<forall> a1:k1. \<sigma>1" "\<tau>1 = \<sigma>1[\<tau>/a1]" by (cases rule: Tm.cases[OF TApp(2)]) auto
  obtain a2 k2 \<sigma>2 where 2: "\<Gamma> , \<Delta> \<turnstile> e1 : \<forall> a2:k2. \<sigma>2" "\<tau>2 = \<sigma>2[\<tau>/a2]" by (cases rule: Tm.cases[OF TApp(3)]) auto
  show ?case using TApp(1)[OF 1(1) 2(1)] subst_type_same 1(2) 2(2) by simp
next
  case (Ctor x)
  then show ?case using axiom_isin_split axiom_isin_same(2) axioms_valid(3)[OF Ctor(2)] by blast
next
  case (Lam x \<tau> e)
  then show ?case by (metis T_Abs_Inv)
next
  case (TyLam a k e)
  then show ?case by (metis T_AbsT_Inv)
next
  case (Let x \<tau> e1 e2)
  then show ?case using T_Let_Inv by blast
qed

end
