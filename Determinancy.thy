theory Determinancy
  imports Typing Typing_Lemmas
begin

lemma unique_ty: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k1 ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<rbrakk> \<Longrightarrow> k1 = k2"
proof (nominal_induct \<tau> arbitrary: k1 k2 rule: \<tau>_tlist.strong_induct(1)[of _ "\<lambda>a b. True"])
  case (TyVar x)
  then show ?case using isin_split isin_same(1) by blast
next
  case (TyData T tys)
  then show ?case
  proof (induction tys arbitrary: k1 k2 rule: \<tau>_tlist.inducts(2)[of "\<lambda>x. True"])
    case TNil
    then show ?case using axiom_isin_split axiom_isin_same(1) axioms_valid(2)[OF TyData(2)] by blast 
  next
    case (TCons \<sigma> tys)
    then show ?case by fastforce
  qed auto
next
  case (TyApp e1 e2)
  then show ?case by fastforce
next
  case (TyForall x1 x2 x3)
  then show ?case by (metis Ty_Forall_Inv_2)
qed auto

lemma unique_tm: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 ; \<Gamma> , \<Delta> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<tau>1 = \<tau>2"
proof (nominal_induct e avoiding: \<Gamma> \<tau>1 \<tau>2 rule: term_elist.strong_induct(1)[of _ "\<lambda>a b. True"])
  case (Var x)
  then show ?case using isin_split isin_same(2) by blast
next
  case (Ctor D tys vals)
  then show ?case
  proof (induction vals arbitrary: \<tau>1 \<tau>2 rule: term_elist.inducts(2)[of "\<lambda>x. True"])
    case ENil
    then show ?case
    proof (induction tys arbitrary: \<tau>1 \<tau>2 rule: \<tau>_tlist.inducts(2)[of "\<lambda>x. True"])
      case TNil
      then show ?case using axiom_isin_split axiom_isin_same(2) axioms_valid(3)[OF Ctor(2)] by blast
    next
      case (TCons x1 x2)
      have "\<Gamma> , \<Delta> \<turnstile> TApp (Ctor D x2 ENil) x1 : \<tau>1" using TCons(4) by blast
      then obtain \<sigma>1 a1 k1 where P1: "\<Gamma> , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall> a1:k1. \<sigma>1" "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k1" "\<tau>1 = \<sigma>1[x1/a1]" by blast
      have "\<Gamma> , \<Delta> \<turnstile> TApp (Ctor D x2 ENil) x1 : \<tau>2" using TCons(5) by blast
      then obtain \<sigma>2 a2 k2 where P2: "\<Gamma> , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall> a2:k2. \<sigma>2" "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k2" "\<tau>2 = \<sigma>2[x1/a2]" by blast
      have "(\<forall> a1:k1. \<sigma>1) = (\<forall> a2:k2. \<sigma>2)" using TCons P1(1) P2(1) by blast
      then show ?case using P1(3) P2(3) \<tau>_tlist.eq_iff(5) subst_type_same by blast
    qed simp_all
  next
    case (ECons x1 x2)
    from ECons(4,5) have "\<Gamma> , \<Delta> \<turnstile> App (Ctor D tys x2) x1 : \<tau>1" "\<Gamma> , \<Delta> \<turnstile> App (Ctor D tys x2) x1 : \<tau>2" by auto
    then obtain \<tau>1' \<tau>2' where "\<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1' \<rightarrow> \<tau>1" "\<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>2' \<rightarrow> \<tau>2" by blast
    then have "(\<tau>1' \<rightarrow> \<tau>1) = (\<tau>2' \<rightarrow> \<tau>2)" using ECons(2) by blast
    then show ?case by simp
  qed simp_all
next
  case (TApp e1 \<tau>)
  obtain a1 k1 \<sigma>1 where 1: "\<Gamma> , \<Delta> \<turnstile> e1 : \<forall> a1:k1. \<sigma>1" "\<tau>1 = \<sigma>1[\<tau>/a1]" by (cases rule: Tm.cases[OF TApp(2)]) auto
  obtain a2 k2 \<sigma>2 where 2: "\<Gamma> , \<Delta> \<turnstile> e1 : \<forall> a2:k2. \<sigma>2" "\<tau>2 = \<sigma>2[\<tau>/a2]" by (cases rule: Tm.cases[OF TApp(3)]) auto
  show ?case using TApp(1)[OF 1(1) 2(1)] subst_type_same 1(2) 2(2) by simp
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
