theory Soundness
  imports Typing Semantics Typing_Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

declare term_elist.fv_defs[simp]
declare \<tau>_tlist.fv_defs[simp]

theorem progress: "[] , \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<longrightarrow> e')"
proof (induction "[] :: \<Gamma>" \<Delta> e \<tau> rule: Tm.induct)
  case (Tm_App \<Delta> e1 \<tau>1 \<tau>2 e2)
  note IH1 = Tm_App(2)
  note IH2 = Tm_App(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_value e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_value e2"
      from \<open>is_value e1\<close> Tm_App(1) have "(\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)) \<or> (\<exists>D tys vals. e1 = Ctor D tys vals)" by (simp add: fun_ty_lam)
      then have "\<exists>e'. Step (App e1 e2) e'" using \<open>is_value e2\<close> ST_BetaI ST_CtorApp by blast
      then show ?thesis by simp
    next
      assume "\<exists>e2'. Step e2 e2'"
      then show ?thesis using ST_BetaI ST_CtorApp Tm_App.hyps(1) \<open>is_value e1\<close> fun_ty_lam by metis
    qed
  next
    assume "\<exists>e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
next
  case (Tm_Let e1 \<tau>1 x e2 \<tau>2)
  then show ?case using ST_SubstI by blast
next
  case (Tm_TApp \<Delta> e a k \<sigma> \<tau>)
  from Tm_TApp(2) show ?case
  proof (elim disjE)
    assume "is_value e"
    then have "(\<exists>b k e1. e = (\<Lambda> b : k . e1)) \<or> (\<exists>D tys vals. e = Ctor D tys vals)" using Tm_TApp.hyps(1) forall_ty_lam by blast
    then show ?thesis using Step.ST_BetaTI Step.ST_CtorTApp Tm_TApp by blast
  next
    assume "\<exists>e'. Step e e'"
    then show ?thesis using ST_AppTI by fast
  qed
qed auto

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

lemma weaken_ty:
  shows "\<lbrakk> \<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
  and "\<lbrakk> \<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k"
proof (nominal_induct \<tau> and tys avoiding: \<Gamma> \<Gamma>' xs k T rule: \<tau>_tlist.strong_induct)
  case (TyVar x)
  then have 1: "BTyVar x k \<in> (\<Gamma> @ \<Gamma>')" by blast
  show ?case by (rule Ty_Var[OF TyVar(2) weaken_isin[OF 1 TyVar(2)]])
next
  case (TyData x1 x2)
  then show ?case by simp
next
  case TyArrow
  then have "k = (\<star> \<rightarrow> \<star> \<rightarrow> \<star>)" by blast
  then show ?case using Ty_Arrow[OF TyArrow(2)] by argo
next
  case (TyApp \<tau>1 \<tau>2)
  obtain k1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : k1 \<rightarrow> k" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by (cases rule: Ty.cases[OF TyApp(3)]) auto
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow k1 k" by (rule TyApp(1)[OF P(1) TyApp(4)])
  have 3: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by (rule TyApp(2)[OF P(2) TyApp(4)])
  show ?case by (rule Ty_App[OF 2 3])
next
  case (TyForall a k1 \<sigma>)
  have P: "(BTyVar a k1 # \<Gamma>) @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" "k = \<star>" using Ty_Forall_Inv[OF TyForall(7)] TyForall(1,2) fresh_append by auto
  have 1: "atom a \<sharp> \<Gamma> @ xs @ \<Gamma>'" using TyForall(1-3) fresh_append by blast
  have 2: "\<Delta> \<turnstile> (BTyVar a k1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_TyVar[OF TyForall(8) 1] by simp
  have 3: "BTyVar a k1 # \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using TyForall(6)[OF P(1) 2] by simp
  show ?case using Ty_Forall[OF 3] P(2) by simp
next
  case TNil
  then have "AxData T k \<in> set \<Delta>" by blast
  then show ?case using Ty_Data[OF TNil(2)] by simp
next
  case (TCons x1 x2)
  then obtain k1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T x2 : k1 \<rightarrow> k" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k1" by blast
  have 1: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T x2 : k1 \<rightarrow> k" by (rule TCons(2)[OF P(1) TCons(4)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k1" by (rule TCons(1)[OF P(2) TCons(4)])
  show ?case by (rule Ty_DataApp[OF 1 2])
qed

lemma weaken_axioms_ty:
  shows "\<lbrakk> \<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; \<Delta>' @ xs @ \<Delta> \<turnstile> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> ,  \<Delta>' @ xs @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
  and "\<lbrakk> \<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k ; \<Delta>' @ xs @ \<Delta> \<turnstile> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> ,  \<Delta>' @ xs @ \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T tys : k"
proof (nominal_induct \<tau> and tys avoiding: \<Delta> \<Delta>' k xs T \<Gamma> rule: \<tau>_tlist.strong_induct)
  case (TyApp \<tau>1 \<tau>2)
  then show ?case using Ty_App by blast
next
  case (TyForall a k1 \<sigma>)
  have P: "BTyVar a k1 # \<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" "k = \<star>" using Ty_Forall_Inv[OF TyForall(8,6)] by auto
  have 1: "BTyVar a k1 # \<Gamma> , \<Delta>' @ xs @ \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" by (rule TyForall(7)[OF P(1) Ctx_TyVar[OF TyForall(9,6)]])
  show ?case using Ty_Forall[OF 1] P(2) by argo
next
  case (TCons x1 x2)
  then obtain k1 where "\<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y TyData T x2 : k1 \<rightarrow> k" "\<Gamma> , \<Delta>' @ \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k1" by blast
  then show ?case using TCons Ty_DataApp by blast
qed (auto intro: Ty_intros)

lemma weaken_tm:
  shows "\<lbrakk> \<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> e : \<tau> ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e : \<tau>"
  and "\<lbrakk> \<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> Ctor D tys vals : \<tau> ; \<Delta> \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> Ctor D tys vals : \<tau>"
proof (nominal_induct e and vals avoiding: \<Gamma> \<Gamma>' xs \<tau> D tys rule: term_elist.strong_induct)
  case (Var x)
  then have 1: "BVar x \<tau> \<in> (\<Gamma> @ \<Gamma>')" by (cases rule: Tm.cases[OF Var(1)]) auto
  have 2: "BVar x \<tau> \<in> (\<Gamma> @ xs @ \<Gamma>')" by (rule weaken_isin[OF 1 Var(2)])
  show ?case by (rule Tm_Var[OF Var(2) 2])
next
  case (App e1 e2)
  obtain \<tau>1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> e2 : \<tau>1" by (cases rule: Tm.cases[OF App(3)]) auto
  have 1: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" by (rule App(1)[OF P(1) App(4)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e2 : \<tau>1" by (rule App(2)[OF P(2) App(4)])
  show ?case by (rule Tm_App[OF 1 2])
next
  case (TApp e \<sigma>)
  obtain a k \<sigma>1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> e : \<forall> a:k. \<sigma>1" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k" "\<tau> = \<sigma>1[\<sigma>/a]" by (cases rule: Tm.cases[OF TApp(2)]) auto
  have 1: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e : \<forall> a:k. \<sigma>1" by (rule TApp(1)[OF P(1) TApp(3)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k" by (rule weaken_ty(1)[OF P(2) TApp(3)])
  show ?case using Tm_TApp[OF 1 2] P(3) by simp
next
  case (Ctor x1 x2 x3)
  then show ?case by simp
next
  case (Lam x \<tau>1 e)
  have 1: "atom x \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append Lam(1,2) by blast
  obtain \<tau>2 where P: "(BVar x \<tau>1 # \<Gamma>) @ \<Gamma>' , \<Delta> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" using T_Abs_Inv[OF Lam(8) 1] by auto
  have 2: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using P(1) context_regularity[of _ "[]"] context_valid(2)[OF P(1)] by auto
  have 3: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule weaken_ty(1)[OF 2 Lam(9)])
  have 4: "atom x \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append Lam(1-3) by blast
  have 5: "\<Delta> \<turnstile> (BVar x \<tau>1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_Var[OF 3 4] by simp
  have 6: "BVar x \<tau>1 # \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e : \<tau>2" using Lam(7)[OF P(1) 5] by simp
  show ?case using Tm_Abs[OF 6] P(2) by simp
next
  case (TyLam a k e)
  have 1: "atom a \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append TyLam(1,2) by blast
  obtain \<sigma> where P: "(BTyVar a k # \<Gamma>) @ \<Gamma>' , \<Delta> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a : k . \<sigma>)" using T_AbsT_Inv[OF TyLam(8) 1 TyLam(4)] by auto
  have 2: "atom a \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append TyLam(1-3) by blast
  have 3: "\<Delta> \<turnstile> (BTyVar a k # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_TyVar[OF TyLam(9) 2] by simp
  have 4: "BTyVar a k # \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e : \<sigma>" using TyLam(7)[OF P(1) 3] by simp
  show ?case using Tm_TAbs[OF 4] P(2) by simp
next
  case (Let x \<tau>1 e1 e2)
  have 1: "atom x \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append Let(1,2) by blast
  have P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> e1 : \<tau>1" "(BVar x \<tau>1 # \<Gamma>) @ \<Gamma>' , \<Delta> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let(9) 1] by auto
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e1 : \<tau>1" by (rule Let(7)[OF P(1) Let(10)])
  have 3: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using P(2) context_regularity context_valid(2)[OF P(2)] by auto
  have 4: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule weaken_ty(1)[OF 3 Let(10)])
  have 5: "atom x \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append Let(1-3) by blast
  have 6: "\<Delta> \<turnstile> (BVar x \<tau>1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_Var[OF 4 5] by simp
  have 7: "BVar x \<tau>1 # \<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> e2 : \<tau>" using Let(8)[OF P(2) 6] by simp
  show ?case by (rule Tm_Let[OF 2 7])
next
  case ENil
  then show ?case
  proof (induction tys arbitrary: \<tau> rule: \<tau>_tlist.inducts(2)[of "\<lambda>x. True"])
    case TNil
    then have 1: "AxCtor D \<tau> \<in> set \<Delta>" by blast
    show ?case by (rule Tm_Ctor[OF ENil(2) 1])
  next
    case (TCons x1 x2)
    then obtain a k \<sigma> where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall>a:k. \<sigma>" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k" "\<tau> = \<sigma>[x1/a]" by blast
    have 1: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall> a : k . \<sigma>" by (rule TCons(2)[OF P(1) ENil(2)])
    have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k" by (rule weaken_ty(1)[OF P(2) ENil(2)])
    show ?case using Tm_CtorTApp[OF 1 2] P(3) by simp
  qed auto
next
  case (ECons x1 x2)
  then obtain \<tau>1 where P: "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma> @ \<Gamma>' , \<Delta> \<turnstile> x1 : \<tau>1" by blast
  have 1: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>" by (rule ECons(2)[OF P(1) ECons(4)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' , \<Delta> \<turnstile> x1 : \<tau>1" by (rule ECons(1)[OF P(2) ECons(4)])
  show ?case by (rule Tm_CtorApp[OF 1 2])
qed
lemmas weaken = weaken_isin weaken_ty(1) weaken_tm(1) weaken_axioms_ty(1)

lemma strengthen_aux:
    shows "(\<Delta> \<turnstile> (\<Gamma>' @ BVar x \<tau> # \<Gamma>) \<longrightarrow> \<Delta> \<turnstile> (\<Gamma>' @ \<Gamma>))"
    and "((\<Gamma>' @ BVar x \<tau> # \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<longrightarrow> (\<Gamma>' @ \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k)"
proof (induction rule: Ctx_Ty_induct_split)
  case (Ctx_TyVar \<Gamma>' b k2)
  then show ?case by (metis Ctx.simps append_Cons fresh_Cons fresh_append)
next
  case (Ctx_Var \<Gamma>' \<tau> x)
  then show ?case by (metis Ctx.simps append_Cons fresh_Cons fresh_append)
next
  case (Ty_Var \<Gamma>' b k2)
  then show ?case using Ax_Ctx_Ty.Ty_Var isin_superset_tyvar by blast
qed (auto intro: Ty_intros)

corollary strengthen_context: "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>' @ \<Gamma>"
  using strengthen_aux context_split_valid by blast
corollary strengthen_ty: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
  using strengthen_aux context_split_valid context_valid(1) by blast

lemma strengthen_tm:
  shows "\<lbrakk> atom x \<sharp> e ; \<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e : \<tau>'"
  and "\<lbrakk> atom x \<sharp> vals ; \<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals : \<tau>'"
proof (nominal_induct e and vals avoiding: \<tau>' \<Gamma>' x \<tau> \<Gamma> D tys rule: term_elist.strong_induct)
  case (Var y)
  then show ?case using Tm_Var isin_superset_var strengthen_aux(1) by force
next
  case (App x1 x2)
  then obtain \<tau>1 where P: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1 \<rightarrow> \<tau>'" "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> x2 : \<tau>1" by blast
  have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1 \<rightarrow> \<tau>'" using App(1)[OF _ P(1)] App(3) by simp
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> x2 : \<tau>1" using App(2)[OF _ P(2)] App(3) by simp
  show ?case by (rule Tm_App[OF 1 2])
next
  case (TApp e \<tau>2)
  then obtain a k \<sigma> where P: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e : \<forall>a:k. \<sigma>" "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k"  "\<tau>' = \<sigma>[\<tau>2/a]" by blast
  then have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e : \<forall> a : k . \<sigma>" using TApp by simp
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k" by (rule strengthen_ty[OF P(2)])
  show ?case using Tm_TApp[OF 1 2] P(3) by simp
next
  case (Ctor D tys vals)
  then show ?case by simp
next
  case (Lam y \<tau>1 e)
  have 1: "atom y \<sharp> \<Gamma>' @ BVar x \<tau> # \<Gamma>" using Lam(2-5) fresh_Cons fresh_append by force
  obtain \<tau>2 where P: "(BVar y \<tau>1 # \<Gamma>') @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" "\<tau>' = (\<tau>1 \<rightarrow> \<tau>2)" using T_Abs_Inv[OF Lam.prems(2) 1] by auto
  have 2: "atom x \<sharp> e" using Lam(3,9) fresh_at_base(2) by auto
  have 3: "BVar y \<tau>1 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" using Lam(8)[OF 2 P(1)] by simp
  show ?case using Tm_Abs[OF 3] P(2) by simp
next
  case (TyLam a k e)
  have 1: "atom a \<sharp> \<Gamma>' @ BVar x \<tau> # \<Gamma>" using TyLam(2-5) fresh_Cons fresh_append by force
  obtain \<sigma> where P: "(BTyVar a k # \<Gamma>') @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e : \<sigma>" "\<tau>' = (\<forall> a : k . \<sigma>)" using T_AbsT_Inv[OF TyLam.prems(2) 1 TyLam(1)] by auto
  have 2: "BTyVar a k # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e : \<sigma>" using TyLam(8)[OF _ P(1)] TyLam(9) by simp
  then show ?case using Tm_TAbs[OF 2] P(2) by simp
next
  case (Let y \<tau>1 e1 e2)
  have 1: "atom y \<sharp> \<Gamma>' @ BVar x \<tau> # \<Gamma>" using Let(2-5) fresh_Cons fresh_append by force
  have P: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1" "(BVar y \<tau>1 # \<Gamma>') @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>'" using T_Let_Inv[OF Let.prems(2) 1] by auto
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1" using Let(8)[OF _ P(1)] Let.prems(1) by simp
  have 3: "atom x \<sharp> e2" using Let(3) Let.prems(1) fresh_at_base(2) by auto
  have 4: "BVar y \<tau>1 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>'" using Let(9)[OF 3 P(2)] by simp
  show ?case by (rule Tm_Let[OF 2 4])
next
  case ENil
  then show ?case
  proof (induction tys arbitrary: \<tau>' rule: \<tau>_tlist.inducts(2)[of "\<lambda>x. True"])
    case TNil
    then show ?case using Tm_Ctor strengthen_context by auto
  next
    case (TCons x1 x2)
    then obtain a k \<sigma> where P: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall>a:k. \<sigma>" "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k" "\<tau>' = \<sigma>[x1/a]" by blast
    have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall> a : k . \<sigma>" by (rule TCons(2)[OF TCons(3) P(1)])
    have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k" by (rule strengthen_ty[OF P(2)])
    show ?case using Tm_CtorTApp[OF 1 2] P(3) by simp
  qed auto
next
  case (ECons x1 x2)
  then obtain \<tau>1 where P: "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>'" "\<Gamma>' @ BVar x \<tau> # \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1" by blast
  have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>'" using ECons(2)[OF _ P(1)] ECons(3) by simp
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1" using ECons(1)[OF _ P(2)] ECons(3) by simp
  show ?case by (rule Tm_CtorApp[OF 1 2])
qed
lemmas strengthen = strengthen_context strengthen_ty strengthen_tm(1)

lemma type_substitution_aux:
  assumes "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
  shows "(\<Delta> \<turnstile> (\<Gamma>' @ BTyVar a k # \<Gamma>) \<longrightarrow> \<Delta> \<turnstile> (subst_context \<Gamma>' \<sigma> a @ \<Gamma>))"
    and "((\<Gamma>' @ BTyVar a k # \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> (subst_context \<Gamma>' \<sigma> a @ \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y subst_type \<tau> \<sigma> a : k2)"
proof (induction rule: Ctx_Ty_induct_split)
  case (Ctx_TyVar \<Gamma>' b k2)
  then have "atom b \<sharp> \<sigma>" using assms fresh_Cons fresh_append fresh_in_context_ty by blast
  then have 1: "atom b \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson Ctx_TyVar(3) fresh_Cons fresh_append fresh_subst_context_tyvar)
  show ?case using Ax_Ctx_Ty.Ctx_TyVar[OF Ctx_TyVar(2) 1] assms by auto
next
  case (Ctx_Var \<Gamma>' \<tau> x)
  have 1: "atom x \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson Ctx_Var(3) fresh_Cons fresh_append fresh_subst_context_var)
  show "\<Delta> \<turnstile> (BVar x \<tau> # \<Gamma>')[\<sigma>/a] @ \<Gamma>" using Ax_Ctx_Ty.Ctx_Var[OF Ctx_Var(2) 1] by simp
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
proof (induction \<Gamma> \<Delta> e \<tau> rule: Tm.induct)
  case (Tm_Var \<Delta> \<Gamma> x \<tau>)
  then obtain \<Gamma>1 \<Gamma>2 where 1: "\<Gamma> = \<Gamma>1 @ BVar x \<tau> # \<Gamma>2" using isin_split by blast
  then have "\<Gamma>2, \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using context_regularity Tm_Var(1) by blast
  then show ?case using weaken(2)[of "[]" \<Gamma>2 \<Delta> \<tau> \<star> "\<Gamma>1 @ [BVar x \<tau>]"] Tm_Var(1) 1 by simp
next
  case (Tm_Abs x \<tau>1 \<Gamma> \<Delta> e \<tau>2)
  have 1: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using context_regularity context_valid(1)[OF Tm_Abs(2)] by blast
  have 2: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" using strengthen_ty[of "[]"] Tm_Abs(2) by force
  have 3: "\<Delta> \<turnstile> \<Gamma>" by (rule context_valid(1)[OF 1])
  show ?case by (rule Ty_App[OF Ty_App[OF Ty_Arrow[OF 3] 1] 2])
next
  case (Tm_TApp \<Gamma> \<Delta> e a k \<sigma> \<tau>)
  obtain a' \<sigma>' where P: "(\<forall> a:k. \<sigma>) = (\<forall> a':k. \<sigma>')" "BTyVar a' k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" by (cases rule: Ty.cases[OF Tm_TApp(3)]) auto
  have "\<Gamma>, \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<tau>/a'] : \<star>" using type_substitution_ty[of "[]", OF _ Tm_TApp(2)] P by auto
  then show ?case using P(1) subst_type_same by auto
next
  case (Tm_Ctor \<Delta> \<Gamma> D \<tau>)
  have 1: "\<turnstile> \<Delta>" by (rule axioms_valid(1)[OF Tm_Ctor(1)])
  then obtain \<Delta>1 \<Delta>2 where P: "\<Delta> = \<Delta>1 @ AxCtor D \<tau> # \<Delta>2" using axiom_isin_split[OF Tm_Ctor(2)] by blast
  then have "[] , \<Delta>2 \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using axioms_regularity 1 by simp
  then have "[] , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using weaken(4)[of _ "[]" _ _ _ "\<Delta>1 @ [AxCtor D \<tau>]"] P 1 Ctx_Empty by simp
  then show ?case using weaken(2)[of "[]" "[]"] Tm_Ctor(1) by simp
next
  case (Tm_CtorTApp \<Gamma> \<Delta> D tys a k \<sigma> \<tau>)
  obtain a' \<sigma>' where P: "BTyVar a' k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" "(\<forall>a:k. \<sigma>) = (\<forall>a':k. \<sigma>')" using Ty_Forall_Inv_2[OF Tm_CtorTApp(3)] by metis
  then have 1: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<tau>/a'] : \<star>" using type_substitution_ty[of "[]"] Tm_CtorTApp(2) by simp
  have "\<sigma>'[\<tau>/a'] = \<sigma>[\<tau>/a]" using subst_same(3)[of a \<sigma> a' \<sigma>'] P(2) by auto
  then show ?case using 1 by argo
next
  case (Tm_Let \<Gamma> e1 \<tau>1 x e2 \<tau>2)
  then show ?case using strengthen_ty[of "[]"] by force
qed (auto intro: Ty_intros)

lemma isin_subst_var: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> Var x : \<tau> \<Longrightarrow> BVar x \<tau>[\<sigma>/a] \<in> (\<Gamma>'[\<sigma>/a] @ \<Gamma>)"
proof (induction \<Gamma>')
  case Nil
  then have "atom a \<sharp> \<tau>" by (metis CtxE(1) TmE(1) Tm_Var append_eq_Cons_conv fresh_in_context_ty isin.simps(3) typing_regularity)
  then show ?case using Nil.prems fresh_subst_type_same by auto
next
  case (Cons bndr \<Gamma>')
  then show ?case using Tm_Var by (cases bndr rule: binder.exhaust) auto
qed

lemma type_substitution_term:
  shows "\<lbrakk> \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e[\<sigma>/a] : \<tau>[\<sigma>/a]"
and "\<lbrakk> \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals : \<tau> ; \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys[\<sigma>/a] vals[\<sigma>/a] : \<tau>[\<sigma>/a]"
proof (nominal_induct e and vals avoiding: \<tau> a \<sigma> \<Gamma>' \<Gamma> tys D rule: term_elist.strong_induct)
  case (Var x)
  then have P: "\<Delta> \<turnstile> \<Gamma>' @ BTyVar a k # \<Gamma>" "BVar x \<tau> \<in> (\<Gamma>' @ BTyVar a k # \<Gamma>)" by auto
  have 1: "\<Delta> \<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (rule type_substitution_context[OF P(1) Var(2)])
  then show ?case using Tm_Var[OF 1] Var isin_subst_var by auto
next
  case (App e1 e2)
  obtain \<tau>1 where P: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>1" by (cases rule: Tm.cases[OF App(3)]) auto
  have 1: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e1[\<sigma>/a] : \<tau>1[\<sigma>/a] \<rightarrow> \<tau>[\<sigma>/a]" using App(1)[OF P(1) App(4)] by simp
  have 2: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e2[\<sigma>/a] : \<tau>1[\<sigma>/a]" by (rule App(2)[OF P(2) App(4)])
  show ?case using Tm_App[OF 1 2] by simp
next
  case (TApp e \<tau>2)
  obtain b k2 \<sigma>' where P: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : (\<forall> b:k2. \<sigma>')" "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k2" "\<tau> = \<sigma>'[\<tau>2/b]" by (cases rule: Tm.cases[OF TApp(2)]) auto
  obtain c::tyvar where "atom c \<sharp> (a, b, \<Gamma>, \<Gamma>', \<sigma>, \<sigma>', \<tau>2)" using obtain_fresh by blast
  then have c: "atom c \<sharp> \<sigma>'" "atom c \<sharp> \<sigma>" "atom c \<sharp> a" by auto
  obtain \<sigma>2 where 1: "(\<forall> b:k2. \<sigma>') = (\<forall> c:k2. \<sigma>2)" using Abs_lst_rename[OF c(1)] by auto
  then have 2: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : (\<forall> c:k2. \<sigma>2)" using P(1) by argo
  have 3: "\<tau> = \<sigma>2[\<tau>2/c]" using subst_type_same 1 P(3) by simp
  have 4: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e[\<sigma>/a] : (\<forall> c : k2 . \<sigma>2[\<sigma>/a])" using TApp(1)[OF 2 TApp(3)] c(2,3) by simp
  have 5: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>2[\<sigma>/a] : k2" by (rule type_substitution_ty[OF P(2) TApp(3)])
  show ?case using Tm_TApp[OF 4 5] subst_subst(3)[of c a \<sigma> \<sigma>2 \<tau>2] 3 c(2,3) by simp
next
  case (Ctor D x2 x3)
  then show ?case by simp
next
  case (Lam x \<tau>1 e)
  have 1: "atom x \<sharp> \<Gamma>' @ BTyVar a k # \<Gamma>" using fresh_Cons fresh_append Lam(2,4,5) by force
  obtain \<tau>2 where P: "BVar x \<tau>1 # \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" by (rule T_Abs_Inv[OF Lam.prems(1) 1])
  then have 2: "BVar x \<tau>1[\<sigma>/a] # \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e[\<sigma>/a] : \<tau>2[\<sigma>/a]" using Lam(8)[of "BVar x \<tau>1 # \<Gamma>'"] Lam(10) by simp
  show ?case using Tm_Abs[OF 2] P(2) by simp
next
  case (TyLam b k2 \<sigma>2)
  have 1: "atom b \<sharp> \<Gamma>' @ BTyVar a k # \<Gamma>" using fresh_Cons fresh_append TyLam(2,4,5) by force
  obtain \<sigma>'::\<tau> where P: "BTyVar b k2 # \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> \<sigma>2 : \<sigma>'" "\<tau> = (\<forall> b : k2 . \<sigma>')" by (rule T_AbsT_Inv[OF TyLam.prems(1) 1 TyLam(1)])
  then have 2: "BTyVar b k2 # \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> \<sigma>2[\<sigma>/a] : \<sigma>'[\<sigma>/a]" using TyLam(8)[of "BTyVar b k2 # \<Gamma>'"] TyLam(2,10) by force
  show ?case using Tm_TAbs[OF 2] TyLam(2,3) P(2) by simp
next
  case (Let x \<tau>1 e1 e2)
  have 1: "atom x \<sharp> \<Gamma>' @ BTyVar a k # \<Gamma>" using fresh_Cons fresh_append Let(2,4,5) by force
  have 2: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1" "BVar x \<tau>1 # \<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let.prems(1) 1] by auto
  have 3: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e1[\<sigma>/a] : \<tau>1[\<sigma>/a]" by (rule Let(8)[OF 2(1) Let.prems(2)])
  have 4: "BVar x \<tau>1[\<sigma>/a] # \<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> e2[\<sigma>/a] : \<tau>[\<sigma>/a]" using Let(9)[of "BVar x \<tau>1 # \<Gamma>'"] 2(2) Let.prems(2) by simp
  show ?case using Tm_Let[OF 3 4] by simp
next
  case ENil
  then show ?case
  proof (induction tys arbitrary: \<tau> rule: \<tau>_tlist.inducts(2)[of "\<lambda>x. True"])
    case TNil
    then have 0: "AxCtor D \<tau> \<in> set \<Delta>" by blast
    have 1: "\<Delta> \<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (rule type_substitution_context[OF context_valid(2)[OF TNil(1)] TNil(2)])
    have 2: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D TNil[\<sigma>/a] ENil[\<sigma>/a] : \<tau>" using Tm_Ctor[OF 1] TNil(1) by auto
    have 3: "\<turnstile> \<Delta>" by (rule axioms_valid(1)[OF 1])
    have 4: "atom a \<sharp> \<tau>" using fresh_in_axioms 0 3 axiom.fresh(2) axiom_isin_split fresh_Cons fresh_append by blast
    show ?case using 2 fresh_subst_same(3)[OF 4] by simp
  next
    case (TCons x1 x2)
    then obtain b k' t where P: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> Ctor D x2 ENil : \<forall>b:k'. t" "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y x1 : k'" "\<tau> = t[x1/b]" by blast
    have 1: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta>  \<turnstile>\<^sub>t\<^sub>y x1[\<sigma>/a] : k'" by (rule type_substitution_ty[OF P(2) TCons(4)])
    have 2: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D x2[\<sigma>/a] ENil : (\<forall> b : k' . t)[\<sigma>/a]" using TCons(2)[OF P(1) TCons(4)] by auto
    then obtain c::tyvar where "atom c \<sharp> (b, t, a, \<sigma>)" using obtain_fresh by blast
    then have c: "atom c \<sharp> b" "atom c \<sharp> t" "atom c \<sharp> a" "atom c \<sharp> \<sigma>" by auto
    obtain t' where 3: "(\<forall>b:k'. t) = (\<forall>c:k' . t')" using Abs_lst_rename[OF c(2)] by auto
    then have "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D x2[\<sigma>/a] ENil : (\<forall> c : k' . t')[\<sigma>/a]" using 2 by argo
    then have 4: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D x2[\<sigma>/a] ENil : \<forall> c : k' . t'[\<sigma>/a]" using c(3,4) by simp
    have 5: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D (TCons x1[\<sigma>/a] x2[\<sigma>/a]) ENil : t'[\<sigma>/a][x1[\<sigma>/a]/c]" by (rule Tm_CtorTApp[OF 4 1])
    have 6: "\<tau> = t'[x1/c]" using subst_same(3)[of b t c t'] P(3) 3 by simp
    have "t'[x1/c][\<sigma>/a] = t'[\<sigma>/a][x1[\<sigma>/a]/c]" using subst_subst(3) c(3,4) by simp
    then show ?case using 5 6 by simp
  qed auto
next
  case (ECons x1 x2)
  then obtain \<tau>1 where P: "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma>' @ BTyVar a k # \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1" by blast
  have 1: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys[\<sigma>/a] x2[\<sigma>/a] : \<tau>1[\<sigma>/a] \<rightarrow> \<tau>[\<sigma>/a]" using ECons(2)[OF P(1) ECons(4)] by simp
  have 2: "\<Gamma>'[\<sigma>/a] @ \<Gamma> , \<Delta> \<turnstile> x1[\<sigma>/a] : \<tau>1[\<sigma>/a]" by (rule ECons(1)[OF P(2) ECons(4)])
  then show ?case using Tm_CtorApp[OF 1 2] by simp
qed
lemmas type_substitution = type_substitution_context type_substitution_ty type_substitution_term(1)

lemma substitution:
  shows "\<lbrakk> \<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e : \<tau> ; \<Gamma> , \<Delta> \<turnstile> e' : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e[e'/x] : \<tau>"
  and "\<lbrakk> \<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals : \<tau> ; \<Gamma> , \<Delta> \<turnstile> e' : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys vals[e'/x] : \<tau>"
proof (nominal_induct e and vals avoiding: \<tau> \<Gamma>' x \<Gamma> e' \<sigma> D tys rule: term_elist.strong_induct)
  case (Var y)
  then have P: "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<sigma> # \<Gamma>" "BVar y \<tau> \<in> (\<Gamma>' @ BVar x \<sigma> # \<Gamma>)" by auto
  have 1: "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma>" by (rule strengthen(1)[OF P(1)])
  show ?case
  proof (cases "x = y")
    case True
    then have "\<tau> = \<sigma>" using isin_same(2) P by blast
    then have "\<Gamma> , \<Delta> \<turnstile> (Var y)[e'/x] : \<tau>" using Var(2) True by simp
    then show ?thesis using weaken_tm[of "[]"] 1 by auto
  next
    case False
    then have "BVar y \<tau> \<in> (\<Gamma>' @ \<Gamma>)" using isin_superset(2)[OF P(2,1)] by simp
    then show ?thesis using Tm_Var[OF 1] False by simp
  qed
next
  case (App e1 e2)
  then obtain \<tau>1 where P: "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>1" by auto
  have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e1[e'/x] : \<tau>1 \<rightarrow> \<tau>" by (rule App(1)[OF P(1) App(4)])
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e2[e'/x] : \<tau>1" by (rule App(2)[OF P(2) App(4)])
  show ?case using Tm_App[OF 1 2] by simp
next
  case (TApp e \<tau>1)
  then obtain a k \<sigma>' where P: "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e : \<forall> a:k. \<sigma>'" "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : k" "\<tau> = \<sigma>'[\<tau>1/a]" by blast
  have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e[e'/x] : \<forall> a : k . \<sigma>'" by (rule TApp(1)[OF P(1) TApp(3)])
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : k" by (rule strengthen(2)[OF P(2)])
  show ?case using Tm_TApp[OF 1 2] P(3) by simp
next
  case (Ctor x1 x2 x3)
  then show ?case by simp
next
  case (Lam y \<tau>1 e)
  have 1: "atom y \<sharp> \<Gamma>' @ BVar x \<sigma> # \<Gamma>" using Lam(2-4) fresh_Cons fresh_append by force
  obtain \<tau>2 where P: "BVar y \<tau>1 # \<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" by (rule T_Abs_Inv[OF Lam.prems(1) 1])
  have 2: "BVar y \<tau>1 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e[e'/x] : \<tau>2" using Lam(9)[of "BVar y \<tau>1 # \<Gamma>'"] P(1) Lam.prems(2) by simp
  show ?case using Tm_Abs[OF 2] P(2) Lam(3,5) by simp
next
  case (TyLam a k e)
  have 1: "atom a \<sharp> \<Gamma>' @ BVar x \<sigma> # \<Gamma>" using TyLam(2,4,6) fresh_Cons fresh_append by force
  obtain \<sigma>' where P: "BTyVar a k # \<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e : \<sigma>'" "\<tau> = (\<forall> a : k . \<sigma>')" by (rule T_AbsT_Inv[OF TyLam.prems(1) 1 TyLam(1)])
  have 2: "BTyVar a k # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e[e'/x] : \<sigma>'" using TyLam(9)[of "BTyVar a k # \<Gamma>'"] TyLam.prems(2) P(1) by simp
  show ?case using Tm_TAbs[OF 2] P(2) TyLam(5) by simp
next
  case (Let y \<tau>1 e1 e2)
  have 1: "atom y \<sharp> \<Gamma>' @ BVar x \<sigma> # \<Gamma>" using Let(2-4,6) fresh_Cons fresh_append by force
  have P: "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1" "BVar y \<tau>1 # \<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let.prems(1) 1] by auto
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e1[e'/x] : \<tau>1" by (rule Let(9)[OF P(1) Let.prems(2)])
  have 3: "BVar y \<tau>1 # \<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> e2[e'/x] : \<tau>" using Let(10)[of "BVar y \<tau>1 # \<Gamma>'"] P(2) Let.prems(2) by simp
  show ?case using Tm_Let[OF 2 3] Let(3,5) by simp
next
  case ENil
  then show ?case using strengthen(3)[OF _ ENil(1)] by simp
next
  case (ECons x1 x2)
  then obtain \<tau>1 where P: "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> Ctor D tys x2 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma>' @ BVar x \<sigma> # \<Gamma> , \<Delta> \<turnstile> x1 : \<tau>1" by blast
  have 1: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> Ctor D tys x2[e'/x] : \<tau>1 \<rightarrow> \<tau>" by (rule ECons(2)[OF P(1) ECons(4)])
  have 2: "\<Gamma>' @ \<Gamma> , \<Delta> \<turnstile> x1[e'/x] : \<tau>1" by (rule ECons(1)[OF P(2) ECons(4)])
  then show ?case using Tm_CtorApp[OF 1 2] by simp
qed

theorem preservation:
  fixes e e'::"term"
  assumes "[] \<turnstile> e : \<tau>" "e \<longrightarrow> e'"
  shows "[] \<turnstile> e' : \<tau>"
using assms beta_nf_def value_beta_nf proof (nominal_induct "[]::\<Gamma>" e \<tau> arbitrary: e' rule: Tm.strong_induct)
  case (Tm_App e1 \<tau>1 \<tau>2 e2)
  from Tm_App(5) show ?case
  proof cases
    case (ST_BetaI x \<tau> e)
    then show ?thesis by (metis Tm_App.hyps(1,3) T_Abs_Inv \<tau>.eq_iff(3) append_Nil fresh_Nil substitution)
  next
    case (ST_AppI e2')
    then show ?thesis using Tm_App.hyps(2,3,6) Tm.Tm_App value_beta_nf by blast
  qed
next
  case (Tm_TApp e a k \<sigma> \<tau>)
  from Tm_TApp(4) show ?case
  proof cases
    case (ST_BetaTI b k2 e2)
    obtain c::tyvar where "atom c \<sharp> (a, b, e2, \<sigma>)" using obtain_fresh by blast
    then have c: "atom c \<sharp> a" "atom c \<sharp> b" "atom c \<sharp> e2" "atom c \<sharp> \<sigma>" by auto
    obtain \<sigma>2 where c1: "(\<forall> a:k. \<sigma>) = (\<forall> c:k. \<sigma>2)" using Abs_lst_rename[OF c(4)] by auto
    have same: "k = k2" using Tm_TApp(1) forall_ty_lam ST_BetaTI(1) by fastforce
    obtain e2' where c2: "(\<Lambda> b:k2. e2) = (\<Lambda> c:k. e2')" using Abs_lst_rename[OF c(3)] same by auto
    have 1: "[] \<turnstile> (\<Lambda> c:k. e2') : \<forall> c:k. \<sigma>2" using Tm_TApp(1) ST_BetaTI(1) c2 c1 by simp
    have 2: "[BTyVar c k] \<turnstile> e2' : \<sigma>2"
    proof (cases rule: Tm.cases[OF 1])
      case (4 d _ _ e \<sigma>)
      have x1: "(d \<leftrightarrow> c) \<bullet> e = e2'" using Abs_rename_body[of d e c e2'] 4(2) by simp
      have x2: "(d \<leftrightarrow> c) \<bullet> \<sigma> = \<sigma>2" using Abs_rename_body[of d \<sigma> c \<sigma>2] 4(3) by simp
      show ?thesis
        by (metis "1" Abs1_eq_iff(3) T_AbsT_Inv \<tau>.eq_iff(5) fresh_Nil fresh_in_context_ty typing_regularity)
    qed auto
    then show ?thesis
      by (metis Tm_TApp.hyps(3) \<tau>.eq_iff(5) append_Nil c1 c2 local.ST_BetaTI(2) subst_context.simps(1) subst_term_type_same subst_type_same term.eq_iff(6) type_substitution(3))
  next
    case (ST_AppTI e2)
    then show ?thesis using Tm_TApp(2,3) Tm.Tm_TApp beta_nf_def value_beta_nf by blast
  qed
next
  case (Tm_Let e1 \<tau>1 x e2 \<tau>2)
  from Tm_Let(4) show ?case
  proof cases
    case (ST_SubstI x e2)
    then show ?thesis
      by (metis Tm_Let.hyps(1,3,4) Step.ST_SubstI Step_deterministic append.left_neutral substitution)
  qed
qed auto

lemma multi_preservation: "\<lbrakk> e \<longrightarrow>* e' ; [] \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
  by (induction e e' rule: Steps.induct) (auto simp: preservation)

corollary soundness: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow>* e' \<rbrakk> \<Longrightarrow> \<not>(stuck e')"
  unfolding stuck_def beta_nf_def
  using progress multi_preservation by blast

end
