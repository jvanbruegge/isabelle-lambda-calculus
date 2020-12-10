theory Soundness
  imports Typing Semantics Typing_Lemmas
begin

no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)

declare term.fv_defs[simp]
declare \<tau>.fv_defs[simp]

theorem progress: "[] \<turnstile> e : \<tau> \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<longrightarrow> e')"
proof (induction "[] :: \<Gamma>" e \<tau> rule: T.induct)
case (T_AppI e1 \<tau>1 \<tau>2 e2)
  note IH1 = T_AppI(2)
  note IH2 = T_AppI(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_value e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_value e2"
      from \<open>is_value e1\<close> T_AppI(1) have "\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)" by (simp add: fun_ty_lam)
      then have "\<exists>e'. Step (App e1 e2) e'" using \<open>is_value e2\<close> ST_BetaI by blast
      then show ?thesis by simp
    next
      assume "\<exists>e2'. Step e2 e2'"
      then show ?thesis using ST_BetaI T_AppI.hyps(1) \<open>is_value e1\<close> fun_ty_lam by blast
    qed
  next
    assume "\<exists>e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
next
  case (T_LetI x e1 \<tau>1 e2 \<tau>2)
  then show ?case using ST_SubstI by blast
next
  case (T_AppTI e a \<sigma> \<tau>)
  from T_AppTI(2) show ?case
  proof (elim disjE)
    assume "is_value e"
    then obtain b k e1 where "e = (\<Lambda> b : k . e1)" using T_AppTI
      by (smt T.simps \<tau>.distinct(17) \<tau>.distinct(7) is_value.simps(1) is_value.simps(4) is_value.simps(5) is_value.simps(7))
    then show ?thesis using Step.ST_BetaTI T_AppTI by blast
  next
    assume "\<exists>e'. Step e e'"
    then show ?thesis using ST_AppTI by fast
  qed
qed auto

lemma context_invariance_ty:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
  and has_tyvars: "\<forall>a k. Set.member (atom a) (fv_\<tau> \<tau>) \<and> BTyVar a k \<in> \<Gamma> \<longrightarrow> BTyVar a k \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau> : k"
using assms proof (nominal_induct \<Gamma> \<tau> k avoiding: \<Gamma>' rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using supp_at_base Ty.Ty_Var by fastforce
next
  case (Ty_App \<Gamma> \<tau>1 \<kappa>1 \<kappa>2 \<tau>2)
  then show ?case by (metis Ty.Ty_App UnCI \<tau>.fv_defs(4))
qed (auto intro: Ty.intros)

lemma context_invariance:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  and has_vars: "\<forall>x \<tau>'. Set.member (atom x) (fv_term e) \<and> BVar x \<tau>' \<in> \<Gamma> \<longrightarrow> BVar x \<tau>' \<in> \<Gamma>'"
  and has_tyvars: "\<forall>a k. Set.member (atom a) (fv_term e) \<and> BTyVar a k \<in> \<Gamma> \<longrightarrow> BTyVar a k \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile> e : \<tau>"
using assms proof (nominal_induct \<Gamma> e \<tau> avoiding: \<Gamma>' rule: T.strong_induct)
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then have 1: "BVar x \<tau>1 # \<Gamma>' \<turnstile> e : \<tau>2" by auto
  have 2: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using context_invariance_ty[OF T_AbsI(3)] T_AbsI(7) fv_supp_subset by (simp add: subset_eq)
  show ?case by (rule T.T_AbsI[OF T_AbsI(1) 2 1])
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case by (metis T.T_AppI Un_iff term.fv_defs(2))
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then have 1: "BVar x \<tau>1 # \<Gamma>' \<turnstile> e2 : \<tau>2" by auto
  from T_LetI have 2: "atom x \<sharp> (\<Gamma>', e1)" by auto
  from T_LetI have 3: "\<Gamma>' \<turnstile> e1 : \<tau>1" by force
  show ?case by (rule T.T_LetI[OF 2 1 3])
next
  case (T_AppTI \<Gamma> e a k \<sigma> \<tau>)
  then have 1: "\<Gamma>' \<turnstile> e : \<forall> a : k . \<sigma>" by simp
  have 2: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau> : k" using context_invariance_ty[OF T_AppTI(3)] T_AppTI(5) fv_supp_subset by (simp add: subset_eq)
  show ?case by (rule T.T_AppTI[OF 1 2])
next
  case (T_AbsTI a k \<Gamma> e \<sigma>)
  then have 1: "BTyVar a k # \<Gamma>' \<turnstile> e : \<sigma>" by auto
  have 2: "atom a \<sharp> \<Gamma>'" using T_AbsTI by auto
  show ?case by (rule T.T_AbsTI[OF 1 2])
qed (auto intro: T.intros simp: supp_at_base)

lemma substitution: "\<lbrakk> BVar x \<tau>'#\<Gamma> \<turnstile> e : \<tau> ; [] \<turnstile> v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> subst_term v x e : \<tau>"
proof (nominal_induct e avoiding: \<Gamma> \<tau> v x \<tau>' rule: term.strong_induct)
  case (Var y)
  then show ?case
  proof (cases "y = x")
    case True
    then have "\<tau> = \<tau>'" using T.cases Var(1) by fastforce
    then show ?thesis using True Var(2) context_invariance by fastforce
  next
    case False
    have "fv_term (Var y) = {atom y}" using supp_at_base by auto
    then have "\<Gamma> \<turnstile> Var y : \<tau>" using context_invariance[OF Var(1)] False by auto
    then show ?thesis using False by simp
  qed
next
  case (App e1 e2)
  obtain \<tau>1 where 1: "BVar x \<tau>' # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>)" "BVar x \<tau>' # \<Gamma> \<turnstile> e2 : \<tau>1" by (cases rule: T.cases[OF App(3)]) auto
  have 2: "\<Gamma> \<turnstile> subst_term v x e1 : (\<tau>1 \<rightarrow> \<tau>)" by (rule App(1)[OF 1(1) App(4)])
  have 3: "\<Gamma> \<turnstile> subst_term v x e2 : \<tau>1" by (rule App(2)[OF 1(2) App(4)])
  show ?case using T.T_AppI[OF 2 3] by simp
next
  case (TyApp e1 \<sigma>)
  then show ?case
    by (smt T.cases T_AppTI context_invariance_ty isin.simps(4) subst_term.simps(5) term.distinct(13) term.distinct(23) term.distinct(25) term.distinct(27) term.distinct(29) term.distinct(3) term.eq_iff(3))
next
  case Unit
  have "\<tau> = TyUnit" by (cases rule: T.cases[OF Unit(1)]) auto
  then show ?case using T.T_UnitI by simp
next
  case (Lam y \<sigma> e')
  then have 1: "atom y \<sharp> BVar x \<tau>' # \<Gamma>" by (simp add: fresh_Cons)
  obtain \<tau>2 where P: "BVar y \<sigma> # BVar x \<tau>' # \<Gamma> \<turnstile> e' : \<tau>2" "\<tau> = (\<sigma> \<rightarrow> \<tau>2)" "BVar x \<tau>' # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using T_Abs_Inv[OF Lam(7) 1] by blast
  then have 2: "BVar x \<tau>' # BVar y \<sigma> # \<Gamma> \<turnstile> e' : \<tau>2" using Lam(4) context_invariance by auto
  from P have 3: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using context_invariance_ty by auto
  from Lam show ?case using T.T_AbsI[OF Lam(1) 3] P 2 by auto
next
  case (TyLam a k e)
  have 1: "atom a \<sharp> BVar x \<tau>' # \<Gamma>" by (simp add: TyLam.hyps(1) TyLam.hyps(5) fresh_Cons)
  obtain \<sigma> where P: "BTyVar a k # BVar x \<tau>' # \<Gamma> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a : k . \<sigma>)" using T_AbsT_Inv[OF TyLam(7) 1 TyLam(2)] by blast
  then have 1: "BVar x \<tau>' # BTyVar a k # \<Gamma> \<turnstile> e : \<sigma>" using context_invariance by fastforce
  have 2: "BTyVar a k # \<Gamma> \<turnstile> subst_term v x e : \<sigma>" by (rule TyLam(6)[OF 1 TyLam(8)])
  from TyLam show ?case using T.T_AbsTI[OF 2 TyLam(1)] P by auto
next
  case (Let y \<tau>1 e1 e2)
  then have 1: "atom y \<sharp> BVar x \<tau>' # \<Gamma>" by (simp add: fresh_Cons)
  have P: "BVar x \<tau>' # \<Gamma> \<turnstile> e1 : \<tau>1" "BVar y \<tau>1 # BVar x \<tau>' # \<Gamma> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let(8) 1] by auto
  have 2: "\<Gamma> \<turnstile> subst_term v x e1 : \<tau>1" by (rule Let(6)[OF P(1) Let(9)])
  have 3: "BVar x \<tau>' # BVar y \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>" using Let(4) P(2) context_invariance by auto
  have 4: "BVar y \<tau>1 # \<Gamma> \<turnstile> subst_term v x e2 : \<tau>" by (rule Let(7)[OF 3 Let(9)])
  have "atom y \<sharp> subst_term v x e1" using "2" Let(1) fresh_term_var by blast
  then have 6: "atom y \<sharp> (\<Gamma>, subst_term v x e1)" using Let(1) by auto
  show ?case using T.T_LetI[OF 6 4 2] Let by auto
qed

lemma type_substitution_ty: "\<lbrakk> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau> : k2"
proof (nominal_induct \<tau> avoiding: a \<Gamma> \<tau>' k k2 rule: \<tau>.strong_induct)
 case TyUnit
  then show ?case using context_invariance_ty by auto
next
  case (TyVar x)
  then show ?case
  proof (cases "atom x = atom a")
    case True
    then have "k = k2" using Ty.cases TyVar.prems(1) by force
    then show ?thesis using TyVar True by auto
  next
    case False
    then show ?thesis
      by (smt TyVar.prems(1) TyVar.prems(2) TyVar.prems(3) \<tau>.fv_defs(2) \<tau>.supp(2) context_invariance_ty fresh_def fresh_subst_type isin.simps(5) subst_type.simps(2) ty_fresh_vars)
  qed
next
  case (TyArrow e1 e2)
  then have 1: "k2 = \<star>" using Ty.cases[OF TyArrow(3)] by (smt \<tau>.distinct(15) \<tau>.distinct(9))
  then have "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e1 : \<star>" "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y e2 : \<star>" using Ty.cases[OF TyArrow(3)] by auto
  then show ?case using TyArrow 1 Ty_Arrow by auto
next
  case (TyConApp \<tau>1 \<tau>2)
  then obtain k1 where "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : KArrow k1 k2 \<and> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 : k1" using Ty.cases[OF TyConApp(3)] by fastforce
  then show ?case using TyConApp Ty_App by fastforce
next
  case (TyForall b k3 \<tau>)
  then have "k2 = \<star>" using Ty.cases by fastforce
  have "BTyVar b k3 # BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" proof (cases rule: Ty.cases[OF TyForall(7)])
    case (5 c k4 \<Gamma>2 \<sigma>)
    then have 1: "\<tau> = (b \<leftrightarrow> c) \<bullet> \<sigma>" by (smt Abs1_eq_iff(3) TyForall.prems(1) \<tau>.eq_iff(5) \<tau>.perm_simps(5) flip_at_simps(2) flip_def swap_fresh_fresh ty_fresh_vars)
    from 5 have "k4 = k3" by auto
    then have "(b \<leftrightarrow> c) \<bullet> (BTyVar c k3 # \<Gamma>2 \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>)" using 5(4) by simp
    then have 2: "((b \<leftrightarrow> c) \<bullet> BTyVar c k3) # \<Gamma>2 \<turnstile>\<^sub>t\<^sub>y (b \<leftrightarrow> c) \<bullet> \<sigma> : \<star>" by (smt "5"(1) "5"(4) "5"(5) Cons_eqvt Ty.eqvt TyForall.hyps(1) TyForall.hyps(2) TyForall.hyps(4) \<kappa>.perm_simps(1) \<open>k4 = k3\<close> binder.fresh(2) flip_def fresh_Cons swap_fresh_fresh)
    have "(b \<leftrightarrow> c) \<bullet> BTyVar c k3 = BTyVar b k3" by (simp add: flip_def swap_fresh_fresh)
    then show ?thesis using 1 2 5(1) by argo
  qed auto
  then have 1: "BTyVar a k # BTyVar b k3 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>" using context_invariance_ty TyForall(1) by auto
  have 2: "BTyVar b k3 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using context_invariance_ty[OF TyForall(8)] by (simp add: TyForall.hyps(2) fresh_not_isin_tyvar)
  have 3: "BTyVar b k3 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau> : \<star>" using TyForall(6)[OF 1 2] using TyForall.hyps(1) TyForall.prems(3) fresh_Cons by fastforce
  then show ?case by (simp add: TyForall.hyps(1) TyForall.hyps(2) TyForall.hyps(3) Ty_Forall \<open>k2 = \<star>\<close>)
qed

lemma type_substitution:
  assumes well_typed: "BTyVar a k # \<Gamma> \<turnstile> e : \<sigma>" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k"
  and context_tyvar: "\<forall>b k. BTyVar b k \<in> \<Gamma> \<longrightarrow> BTyVar b k \<in> \<Gamma>'"
  and context_var: "\<forall>x \<tau>. BVar x \<tau> \<in> \<Gamma> \<longrightarrow> BVar x (subst_type \<tau>' a \<tau>) \<in> \<Gamma>'"
  and fresh: "atom a \<sharp> \<Gamma>'"
shows "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<sigma>"
using assms proof (nominal_induct e avoiding: a k \<Gamma> \<Gamma>' \<sigma> \<tau>' rule: term.strong_induct)
  case (Var x)
  then have 1: "BVar x (subst_type \<tau>' a \<sigma>) \<in> \<Gamma>'"
    by (smt T.cases isin.simps(3) term.distinct(1) term.distinct(11) term.distinct(3) term.distinct(5) term.distinct(7) term.distinct(9) term.eq_iff(1))
  show ?case using T.T_VarI[OF 1] by simp
next
  case (App e1 e2)
  obtain \<tau>1 where "BTyVar a k # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<sigma>) \<and> BTyVar a k # \<Gamma> \<turnstile> e2 : \<tau>1" using T.cases[OF App(3)] by fastforce
  then have P: "BTyVar a k # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<sigma>)" "BTyVar a k # \<Gamma> \<turnstile> e2 : \<tau>1" by auto

  have 1: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e1 : subst_type \<tau>' a \<tau>1 \<rightarrow> subst_type \<tau>' a \<sigma>" using App(1)[OF P(1) App(4) App(5) App(6) App(7)] by simp
  have 2: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e2 : subst_type \<tau>' a \<tau>1" by (rule App(2)[OF P(2) App(4) App(5) App(6) App(7)])

  then show ?case using T.T_AppI[OF 1 2] by simp
next
  case (TyApp e \<tau>)

  have "\<exists>b k2 \<sigma>'. BTyVar a k # \<Gamma> \<turnstile> e : (\<forall>b : k2 . \<sigma>') \<and> atom b \<sharp> a \<and> \<sigma> = subst_type \<tau> b \<sigma>' \<and> atom b \<sharp> \<tau>' \<and> BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2"
  proof (cases rule: T.cases[OF TyApp(2)])
    case (6 \<Gamma>2 t b k2 \<sigma>2 \<tau>2)
    then have 1: "BTyVar a k # \<Gamma> \<turnstile> e : \<forall> b : k2 . \<sigma>2" "\<sigma> = subst_type \<tau> b \<sigma>2" "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2" by auto
    obtain c::tyvar where "atom c \<sharp> (a, b, \<sigma>2, \<tau>')" using obtain_fresh by blast
    then have c: "atom c \<sharp> b" "atom c \<sharp> \<sigma>2" "atom c \<sharp> a" "atom c \<sharp> \<tau>'" using fresh_Pair by auto
    from 1(1) have 2: "BTyVar a k # \<Gamma> \<turnstile> e : \<forall> c : k2 . (b \<leftrightarrow> c) \<bullet> \<sigma>2" by (smt Abs1_eq_iff(3) \<tau>.eq_iff(5) c(1) c(2) flip_commute fresh_at_base(2))
    from 1(2) have "\<sigma> = subst_type \<tau> c ((b \<leftrightarrow> c) \<bullet> \<sigma>2)" using subst_type_var_name c by auto
    then show ?thesis using 2 c(3) c(4) 1(3) by blast
  qed auto
  then obtain b k2 \<sigma>' where P: "BTyVar a k # \<Gamma> \<turnstile> e : (\<forall>b : k2 . \<sigma>')" "atom b \<sharp> a" "\<sigma> = subst_type \<tau> b \<sigma>'" "atom b \<sharp> \<tau>'" "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k2" by blast

  have 1: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using context_invariance_ty[OF TyApp(3)] using TyApp.prems(3) by blast
  have 2: "BTyVar a k # \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau> : k2" using context_invariance_ty[OF P(5)] by (smt TyApp.prems(3) isin.simps(5))
  have 3: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau> : k2" by (rule type_substitution_ty[OF 2 1 TyApp(6)])
  have 4: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e : \<forall> b : k2 . subst_type \<tau>' a \<sigma>'" using TyApp(1)[OF P(1) TyApp(3) TyApp(4) TyApp(5) TyApp(6)] P(2) P(4) by auto

  have "\<Gamma>' \<turnstile> TyApp (subst_term_type \<tau>' a e) (subst_type \<tau>' a \<tau>) : subst_type \<tau>' a (subst_type \<tau> b \<sigma>')" using T.T_AppTI[OF 4 3] subst_type_order[OF P(4) P(2)] by simp
  then show ?case using P(3) by simp
next
  case Unit
  then have "\<sigma> = TyUnit" using T.cases by fastforce
  then show ?case using T.T_UnitI by simp
next
  case (Lam x \<tau>1 e)
  then have 1: "atom x \<sharp> BTyVar a k # \<Gamma>" by (simp add: fresh_Cons)
  obtain \<tau>2 where P: "BVar x \<tau>1 # BTyVar a k # \<Gamma> \<turnstile> e : \<tau>2" "\<sigma> = (\<tau>1 \<rightarrow> \<tau>2)" "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using T_Abs_Inv[OF Lam(8) 1] by blast
  then have 2: "BTyVar a k # BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2" using context_invariance[OF P(1)] by simp
  have 3: "BTyVar a k # \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>" using context_invariance_ty[OF P(3)] by (smt Lam.prems(3) isin.simps(5))
  have 4: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using context_invariance_ty[OF Lam(9)] Lam.prems(3) by blast
  have 5: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau>1 : \<star>" using "3" "4" Lam.prems(5) type_substitution_ty by blast
  have 6: "BVar x \<tau>1 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using context_invariance_ty[OF Lam(9)] by auto

  from 4 have 7: "atom a \<sharp> \<tau>'" using Lam.prems(5) ty_fresh_vars by blast
  have 8: "atom a \<sharp> BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>'" using "5" Lam.prems(5) fresh_Cons ty_fresh_vars by fastforce

  have 9: "BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>2" using Lam(7)[OF 2 6 _ _ 8] by (simp add: Lam.prems(3) Lam.prems(4))

  have "\<Gamma>' \<turnstile> \<lambda>x : subst_type \<tau>' a \<tau>1 . subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>1 \<rightarrow> subst_type \<tau>' a \<tau>2" by (rule T.T_AbsI[OF Lam(4) 5 9])
  then show ?case using P(2) by simp
next
  case (TyLam b k2 e)
  then have 1: "atom b \<sharp> BTyVar a k # \<Gamma>" by (simp add: fresh_Cons)
  obtain \<tau> where P: "BTyVar b k2 # BTyVar a k # \<Gamma> \<turnstile> e : \<tau>" "\<sigma> = (\<forall> b : k2 . \<tau>)" using T_AbsT_Inv[OF TyLam(8) 1 TyLam(5)] by blast
  then have 2: "subst_type \<tau>' a \<sigma> = (\<forall> b : k2 . subst_type \<tau>' a \<tau>)" by (simp add: TyLam(1) TyLam(6))
  have 3: "BTyVar a k # BTyVar b k2 # \<Gamma> \<turnstile> e : \<tau>" using context_invariance[OF P(1)] by (smt TyLam.hyps(1) fresh_at_base(2) isin.simps(3) isin.simps(5))
  have 4: "BTyVar b k2 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using context_invariance_ty[OF TyLam(9)] by (simp add: TyLam.hyps(3) fresh_not_isin_tyvar)
  have 5: "atom a \<sharp> BTyVar b k2 # \<Gamma>'" using TyLam(1) TyLam.prems(5) fresh_Cons by fastforce

  have 9: "BTyVar b k2 # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>" using TyLam(7)[OF 3 4 _ _ 5] TyLam(10) TyLam(11) by simp

  show ?case using T.T_AbsTI[OF 9 TyLam(4)] 2 TyLam(1) TyLam(6) by simp
next
  case (Let x \<tau>1 e1 e2)
  then have 1: "atom x \<sharp> BTyVar a k # \<Gamma>" by (simp add: fresh_Cons)
  have P: "BTyVar a k # \<Gamma> \<turnstile> e1 : \<tau>1" "BVar x \<tau>1 # BTyVar a k # \<Gamma> \<turnstile> e2 : \<sigma>" using T_Let_Inv[OF Let(9) 1] by auto
  have 2: "atom x \<sharp> e1" using "1" P(1) fresh_term_var by blast
  have "atom x \<sharp> subst_term_type \<tau>' a e1" using Let P(1) fresh_term_var by blast
  then have 3: "atom x \<sharp> (\<Gamma>', subst_term_type \<tau>' a e1)" using Let(4) by simp
  have 5: "atom a \<sharp> BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>'"
    by (metis Let.hyps(1) Let.prems(2) Let.prems(3) Let.prems(5) binder.fresh(1) context_invariance_ty fresh_Cons fresh_at_base(2) fresh_subst_type ty_fresh_vars)
  have 6: "BTyVar a k # BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<sigma>" using context_invariance[OF P(2)] by auto
  have 7: "BVar x \<tau>1 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' : k" using Let.prems(2) context_invariance_ty isin.simps(4) by blast

  have 9: "BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e2 : subst_type \<tau>' a \<sigma>" using Let(8)[OF 6 7 _ _ 5] Let(11) Let(12) by simp
  show ?case using T.T_LetI[OF 3 9] using Let P(1) by auto
qed

theorem preservation: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow> e' \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
proof (nominal_induct "[] :: \<Gamma>" e \<tau> arbitrary: e' rule: T.strong_induct)
  case T_UnitI
  then show ?case using Step.cases by fastforce
next
  case (T_VarI x \<tau>)
  then show ?case by simp
next
  case (T_AbsI x \<tau>1 e \<tau>2)
  then show ?case using Step.cases by fastforce
next
  case (T_AppI e1 \<tau>1 \<tau>2 e2)
  from \<open>App e1 e2 \<longrightarrow> e'\<close> show ?case
  proof cases
    case (ST_BetaI x \<tau> e)
    then have "\<tau> = \<tau>1" using T_AppI.hyps(1) fun_ty_lam is_value.simps(2) term.eq_iff(5) by blast
    then have 1: "[] \<turnstile> e2 : \<tau>" using T_AppI(3) by simp

    have "[] \<turnstile> \<lambda> x : \<tau> . e : \<tau>1 \<rightarrow> \<tau>2" using T_AppI ST_BetaI by blast
    then have 2: "[BVar x \<tau>] \<turnstile> e : \<tau>2" using T_Abs_Inv fresh_Nil by fastforce

    show ?thesis using substitution[OF 2 1] ST_BetaI by simp
  next
    case (ST_AppI e2)
    then show ?thesis using T_AppI T.T_AppI by blast
  qed
next
  case (T_LetI x e1 \<tau>1 e2 \<tau>2)
  from \<open>Let x \<tau>1 e1 e2 \<longrightarrow> e'\<close> show ?case
  proof cases
    case (ST_SubstI y e)
    then show ?thesis
    proof (cases "atom x = atom y")
      case True
      then show ?thesis by (metis Abs1_eq(3) T_LetI.hyps(3) T_LetI.hyps(4) atom_eq_iff local.ST_SubstI(1) local.ST_SubstI(2) substitution)
    next
      case False
      then have 1: "atom y \<sharp> [(x, \<tau>1)]" by (simp add: fresh_Cons fresh_Nil)
      have "(x \<leftrightarrow> y) \<bullet> e2 = e" by (metis Abs1_eq_iff'(3) False flip_commute local.ST_SubstI(1))
      then have "[BVar y \<tau>1] \<turnstile> e : \<tau>2" using T.eqvt
        by (metis Cons_eqvt Nil_eqvt T_LetI.hyps(3) binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh no_vars_in_ty)
      then show ?thesis using T_LetI ST_SubstI substitution by auto
    qed
  qed
next
  case (T_AppTI e a k \<sigma> \<tau>)
  from T_AppTI(4) show ?case
  proof cases
    case (ST_BetaTI b k2 t)
    obtain c::tyvar where "atom c \<sharp> (a, b, t, \<sigma>)" using obtain_fresh by blast
    then have c: "atom c \<sharp> a" "atom c \<sharp> b" "atom c \<sharp> t" "atom c \<sharp> \<sigma>" using fresh_Pair by auto
    have 1: "[] \<turnstile> (\<Lambda> c : k2 . (b \<leftrightarrow> c) \<bullet> t) : \<forall> c : k2 . (a \<leftrightarrow> c) \<bullet> \<sigma>"
      by (smt Abs1_eq_iff(3) T.cases T_AppTI.hyps(1) \<tau>.distinct(17) \<tau>.distinct(7) \<tau>.eq_iff(5) c(1) c(2) c(3) c(4) flip_commute fresh_at_base(2) is_value.simps(3) is_value.simps(4) is_value.simps(5) is_value.simps(7) isin.simps(1) local.ST_BetaTI(1) term.eq_iff(6))

    have 2: "[BTyVar c k2] \<turnstile> (b \<leftrightarrow> c) \<bullet> t : (a \<leftrightarrow> c) \<bullet> \<sigma>"
    proof (cases rule: T.cases[OF 1])
      case (7 a' k2' \<Gamma> e \<sigma>')
      then have same: "k2 = k2'" using \<tau>.eq_iff(5) by blast
      have 1: "(b \<leftrightarrow> c) \<bullet> t = (a' \<leftrightarrow> c) \<bullet> e"
        by (metis (no_types, lifting) "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_commute flip_def permute_flip_cancel2 permute_plus term.eq_iff(6))
      have 2: "(a \<leftrightarrow> c) \<bullet> \<sigma> = (a' \<leftrightarrow> c) \<bullet> \<sigma>'"
        by (metis "7"(3) Abs1_eq_iff(3) Nominal2_Base.swap_self \<tau>.eq_iff(5) c(4) flip_commute flip_def swap_fresh_fresh)
      from 7(4) have 3: "(a' \<leftrightarrow> c) \<bullet> (BTyVar a' k2' # \<Gamma> \<turnstile> e : \<sigma>')" by simp
      have 4: "(a' \<leftrightarrow> c) \<bullet> (BTyVar a' k2' # \<Gamma>) = ((a' \<leftrightarrow> c) \<bullet> BTyVar a' k2') # \<Gamma>" using "7"(1) by auto
      have 5: "(a' \<leftrightarrow> c) \<bullet> BTyVar a' k2' = BTyVar c k2'" using flip_fresh_fresh[OF no_tyvars_in_kinds[of a' k2'] no_tyvars_in_kinds[of c k2']] flip_at_base_simps(1)[of a' c] by simp

      show ?thesis using T.eqvt[OF 7(4), of "(a' \<leftrightarrow> c)"] using "1" "2" "5" "7"(1) same by auto
    qed auto
    have "k = k2" using T.cases T_AppTI.hyps(1) local.ST_BetaTI(1) by fastforce
    then have "[] \<turnstile> subst_term_type \<tau> c ((b \<leftrightarrow> c) \<bullet> t) : subst_type \<tau> c ((a \<leftrightarrow> c) \<bullet> \<sigma>)" using type_substitution[OF 2 _ _ _ fresh_Nil] T_AppTI(3) by simp
    then show ?thesis using ST_BetaTI(2) subst_term_type_var_name[OF c(3)] subst_type_var_name[OF c(4)] by presburger
  next
    case (ST_AppTI e2)
    then show ?thesis using T.T_AppTI T_AppTI.hyps(2) T_AppTI.hyps(3) by blast
  qed
next
  case (T_AbsTI a e \<sigma>)
  then show ?case using beta_nf_def is_value.simps(3) value_beta_nf by blast
qed

lemma multi_preservation: "\<lbrakk> e \<longrightarrow>* e' ; [] \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
  by (induction e e' rule: Steps.induct) (auto simp: preservation)

corollary soundness: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow>* e' \<rbrakk> \<Longrightarrow> \<not>(stuck e')"
  unfolding stuck_def beta_nf_def
  using progress multi_preservation by blast

end
