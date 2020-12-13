theory Soundness
  imports Typing Semantics Typing_Lemmas
begin

no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)
no_notation Set.member  ("(_/ : _)" [51, 51] 50)

declare term.fv_defs[simp]
declare \<tau>.fv_defs[simp]

theorem progress: "[] \<turnstile> e : \<tau> \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<longrightarrow> e')"
proof (induction "[] :: \<Gamma>" e \<tau> rule: Tm_induct)
case (App e1 e2 \<tau>1 \<tau>2)
  note IH1 = App(2)
  note IH2 = App(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_value e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_value e2"
      from \<open>is_value e1\<close> App(1) have "\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)" by (simp add: fun_ty_lam)
      then have "\<exists>e'. Step (App e1 e2) e'" using \<open>is_value e2\<close> ST_BetaI by blast
      then show ?thesis by simp
    next
      assume "\<exists>e2'. Step e2 e2'"
      then show ?thesis using ST_BetaI App.hyps(1) \<open>is_value e1\<close> fun_ty_lam by blast
    qed
  next
    assume "\<exists>e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
next
  case (Let e1 e2 \<tau>1 \<tau>2 x)
  then show ?case using ST_SubstI by blast
next
  case (TApp a k e \<sigma> \<tau>)
  from TApp(2) show ?case
  proof (elim disjE)
    assume "is_value e"
    then obtain b k e1 where "e = (\<Lambda> b : k . e1)" using TApp.hyps(1) forall_ty_lam by blast
    then show ?thesis using Step.ST_BetaTI TApp by blast
  next
    assume "\<exists>e'. Step e e'"
    then show ?thesis using ST_AppTI by fast
  qed
qed auto

lemma weaken_isin: "\<lbrakk> bndr \<in> (\<Gamma> @ \<Gamma>') ; \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> bndr \<in> (\<Gamma> @ xs @ \<Gamma>')"
proof (induction \<Gamma> arbitrary: bndr \<Gamma>' xs)
  case Nil
  then show ?case by (cases bndr rule: binder.exhaust) (auto simp: isin_subset)
next
  case (Cons b \<Gamma>)
  have 1: "\<turnstile> \<Gamma> @ xs @ \<Gamma>'" using Cons(3) Ctx.cases by auto
  then show ?case
  proof (cases b rule: binder.exhaust)
    case (BVar x \<tau>)
    then show ?thesis using 1 Cons by (cases bndr rule: binder.exhaust) auto
  next
    case (BTyVar a k)
    then show ?thesis using 1 Cons by (cases bndr rule: binder.exhaust) auto
  qed
qed

lemma weaken_ty: "\<lbrakk> \<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
proof (nominal_induct \<tau> avoiding: \<Gamma> \<Gamma>' xs k rule: \<tau>.strong_induct)
  case TyUnit
  then have "k = \<star>" by (cases rule: Ty.cases[OF TyUnit(1)]) auto
  then show ?case using Ty_Unit[OF TyUnit(2)] by simp
next
  case (TyVar x)
  have 1: "BTyVar x k \<in> (\<Gamma> @ \<Gamma>')" by (cases rule: Ty.cases[OF TyVar(1)]) auto
  show ?case by (rule Ty_Var[OF TyVar(2) weaken_isin[OF 1 TyVar(2)]])
next
  case (TyArrow \<tau>1 \<tau>2)
  have "k = \<star> \<and> \<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star> \<and> \<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" by (cases rule: Ty.cases[OF TyArrow(3)]) auto
  then have 1: "k = \<star>" "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" by auto
  have 2: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule TyArrow(1)[OF 1(2) TyArrow(4)])
  have 3: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : \<star>" by (rule TyArrow(2)[OF 1(3) TyArrow(4)])
  show ?case using Ty_FunArrow[OF 2 3] 1(1) by simp
next
  case (TyConApp \<tau>1 \<tau>2)
  obtain k1 where P: "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow k1 k" "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by (cases rule: Ty.cases[OF TyConApp(3)]) auto
  have 2: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow k1 k" by (rule TyConApp(1)[OF P(1) TyConApp(4)])
  have 3: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" by (rule TyConApp(2)[OF P(2) TyConApp(4)])
  show ?case by (rule Ty_App[OF 2 3])
next
  case (TyForall a k1 \<sigma>)
  have P: "(BTyVar a k1 # \<Gamma>) @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" "k = \<star>" using Ty_Forall_Inv[OF TyForall(6)] TyForall(1,2) fresh_append by auto
  have 1: "atom a \<sharp> \<Gamma> @ xs @ \<Gamma>'" using TyForall(1-3) fresh_append by blast
  have 2: "\<turnstile> (BTyVar a k1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_TyVar[OF TyForall(7) 1] by simp
  have 3: "BTyVar a k1 # \<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using TyForall(5)[OF P(1) 2] by simp
  show ?case using Ty_Forall[OF 3] P(2) by simp
qed

lemma weaken_tm: "\<lbrakk> \<Gamma> @ \<Gamma>' \<turnstile> e : \<tau> ; \<turnstile> \<Gamma> @ xs @ \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma> @ xs @ \<Gamma>' \<turnstile> e : \<tau>"
proof (nominal_induct e avoiding: \<Gamma> \<Gamma>' xs \<tau> rule: term.strong_induct)
  case (Var x)
  then have 1: "BVar x \<tau> \<in> (\<Gamma> @ \<Gamma>')" by (cases rule: Tm.cases[OF Var(1)]) auto
  have 2: "BVar x \<tau> \<in> (\<Gamma> @ xs @ \<Gamma>')" by (rule weaken_isin[OF 1 Var(2)])
  show ?case by (rule Tm_Var[OF Var(2) 2])
next
  case (App e1 e2)
  obtain \<tau>1 where P: "\<Gamma> @ \<Gamma>' \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" "\<Gamma> @ \<Gamma>' \<turnstile> e2 : \<tau>1" by (cases rule: Tm.cases[OF App(3)]) auto
  have 1: "\<Gamma> @ xs @ \<Gamma>' \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>" by (rule App(1)[OF P(1) App(4)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' \<turnstile> e2 : \<tau>1" by (rule App(2)[OF P(2) App(4)])
  show ?case by (rule Tm_App[OF 1 2])
next
  case (TyApp e \<sigma>)
  obtain a k \<sigma>1 where P: "\<Gamma> @ \<Gamma>' \<turnstile> e : \<forall> a:k. \<sigma>1" "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<sigma> : k" "\<tau> = \<sigma>1[\<sigma>/a]" by (cases rule: Tm.cases[OF TyApp(2)]) auto
  have 1: "\<Gamma> @ xs @ \<Gamma>' \<turnstile> e : \<forall> a:k. \<sigma>1" by (rule TyApp(1)[OF P(1) TyApp(3)])
  have 2: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<sigma> : k" by (rule weaken_ty[OF P(2) TyApp(3)])
  show ?case using Tm_TApp[OF 1 2] P(3) by simp
next
  case Unit
  then have "\<tau> = TyUnit" by (cases rule: Tm.cases[OF Unit(1)]) auto
  then show ?case using Tm_Unit[OF Unit(2)] by simp
next
  case (Lam x \<tau>1 e)
  have 1: "atom x \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append Lam(1,2) by blast
  obtain \<tau>2 where P: "(BVar x \<tau>1 # \<Gamma>) @ \<Gamma>' \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" using T_Abs_Inv[OF Lam(6) 1] by auto
  have 2: "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (cases rule: Ctx.cases[OF tm_context_valid[OF P(1)]]) auto
  have 3: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule weaken_ty[OF 2 Lam(7)])
  have 4: "atom x \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append Lam(1-3) by blast
  have 5: "\<turnstile> (BVar x \<tau>1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_Var[OF 3 4] by simp
  have 6: "BVar x \<tau>1 # \<Gamma> @ xs @ \<Gamma>' \<turnstile> e : \<tau>2" using Lam(5)[OF P(1) 5] by simp
  show ?case using Tm_Abs[OF 6] P(2) by simp
next
  case (TyLam a k e)
  have 1: "atom a \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append TyLam(1,2) by blast
  obtain \<sigma> where P: "(BTyVar a k # \<Gamma>) @ \<Gamma>' \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a : k . \<sigma>)" using T_AbsT_Inv[OF TyLam(6) 1 TyLam(4)] by auto
  have 2: "atom a \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append TyLam(1-3) by blast
  have 3: "\<turnstile> (BTyVar a k # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_TyVar[OF TyLam(7) 2] by simp
  have 4: "BTyVar a k # \<Gamma> @ xs @ \<Gamma>' \<turnstile> e : \<sigma>" using TyLam(5)[OF P(1) 3] by simp
  show ?case using Tm_TAbs[OF 4] P(2) by simp
next
  case (Let x \<tau>1 e1 e2)
  have 1: "atom x \<sharp> \<Gamma> @ \<Gamma>'" using fresh_append Let(1,2) by blast
  have P: "\<Gamma> @ \<Gamma>' \<turnstile> e1 : \<tau>1" "(BVar x \<tau>1 # \<Gamma>) @ \<Gamma>' \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let(7) 1] by auto
  have 2: "\<Gamma> @ xs @ \<Gamma>' \<turnstile> e1 : \<tau>1" by (rule Let(5)[OF P(1) Let(8)])
  have 3: "\<Gamma> @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (cases rule: Ctx.cases[OF tm_context_valid[OF P(2)]]) auto
  have 4: "\<Gamma> @ xs @ \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" by (rule weaken_ty[OF 3 Let(8)])
  have 5: "atom x \<sharp> \<Gamma> @ xs @ \<Gamma>'" using fresh_append Let(1-3) by blast
  have 6: "\<turnstile> (BVar x \<tau>1 # \<Gamma>) @ xs @ \<Gamma>'" using Ctx_Var[OF 4 5] by simp
  have 7: "BVar x \<tau>1 # \<Gamma> @ xs @ \<Gamma>' \<turnstile> e2 : \<tau>" using Let(6)[OF P(2) 6] by simp
  show ?case by (rule Tm_Let[OF 2 7])
qed

lemma type_substitution_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k"
  shows "(\<turnstile> (\<Gamma>' @ BTyVar a k # \<Gamma>) \<longrightarrow> \<turnstile> (subst_context \<Gamma>' \<sigma> a @ \<Gamma>)) \<and> ((\<Gamma>' @ BTyVar a k # \<Gamma>) \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 \<longrightarrow> (subst_context \<Gamma>' \<sigma> a @ \<Gamma>) \<turnstile>\<^sub>t\<^sub>y subst_type \<tau> \<sigma> a : k2)"
proof (rule Ctx_Ty_induct)
  show "\<turnstile> [][\<sigma>/a] @ \<Gamma>" using ty_context_valid[OF assms(1)] by simp
next
  fix \<Gamma>' a2 k2
  assume a: "\<turnstile> \<Gamma>' @ BTyVar a k # \<Gamma>" "\<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>" "atom (a2::tyvar) \<sharp> \<Gamma>' @ BTyVar a k # \<Gamma>"
  then have "atom a2 \<sharp> \<sigma>" using assms fresh_in_context(2) fresh_Cons fresh_append by blast 
  then have 1: "atom a2 \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson a(3) fresh_Cons fresh_append fresh_subst_context_tyvar)
  show "\<turnstile> (BTyVar a2 k2 # \<Gamma>')[\<sigma>/a] @ \<Gamma>" using Ctx_TyVar[OF a(2) 1] assms by auto
next
  fix \<Gamma>' \<tau> x
  assume a: "\<Gamma>' @ BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" "\<Gamma>'[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>[\<sigma>/a] : \<star>" "atom (x::var) \<sharp> \<Gamma>' @ BTyVar a k # \<Gamma>"
  have 1: "atom x \<sharp> \<Gamma>'[\<sigma>/a] @ \<Gamma>" by (meson a(3) fresh_Cons fresh_append fresh_subst_context_var)
  show "\<turnstile> (BVar x \<tau> # \<Gamma>')[\<sigma>/a] @ \<Gamma>" using Ctx_Var[OF a(2) 1] by simp
next
  fix \<Gamma>' a2 k2
  assume a: "\<turnstile> \<Gamma>' @ BTyVar a k # \<Gamma>" "\<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>" "BTyVar a2 k2 \<in> (\<Gamma>' @ BTyVar a k # \<Gamma>)"
  then show "\<Gamma>'[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y (TyVar a2)[\<sigma>/a] : k2"
  proof (cases "a2 = a")
    case True
    then have "k = k2" using isin_kind_same a by blast
    then have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (TyVar a2)[\<sigma>/a] : k2" using True assms(1) by simp
    then show ?thesis using weaken_ty[of "[]"] a(2) by auto
  next
    case False
    have 1: "BTyVar a2 k2 \<in> (\<Gamma>'[\<sigma>/a] @ \<Gamma>)" by (rule isin_subst[OF a(3,1) False])
    show ?thesis using Ty_Var[OF a(2) 1] False by simp
  qed
next
  fix b k2 \<Gamma>' \<sigma>'
  assume a: "(BTyVar b k2 # \<Gamma>' @ BTyVar a k # \<Gamma>) \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" "(BTyVar b k2 # \<Gamma>')[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<sigma>/a] : \<star>"
  have 1: "a \<noteq> b" by (metis a(1) binder.fresh(2) context_cons_fresh_tyvar fresh_Cons fresh_append fresh_at_base(2) ty_context_valid)
  then have 2: "BTyVar b k2 # \<Gamma>'[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma>'[\<sigma>/a] : \<star>" using a(2) by simp
  show "\<Gamma>'[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall> b : k2 . \<sigma>')[\<sigma>/a] : \<star>" using Ty_Forall[OF 2]
    by (metis "1" "2" assms atom_eq_iff context_cons_fresh_tyvar fresh_Pair fresh_append fresh_at_base(2) subst_type.simps(5) ty_context_valid ty_fresh_vars)
qed (auto intro: Ty_intros)

corollary type_substitution_context: "\<lbrakk> \<turnstile> \<Gamma>' @ BTyVar a k # \<Gamma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>'[\<sigma>/a] @ \<Gamma>"
  using type_substitution_aux by blast
corollary type_substitution_ty: "\<lbrakk> \<Gamma>' @ BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : k \<rbrakk> \<Longrightarrow> \<Gamma>'[\<sigma>/a] @ \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>[\<sigma>/a] : k2"
  using type_substitution_aux by blast

end
