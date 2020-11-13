theory Soundness
  imports Defs
begin

no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (nominal_induct \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: T.strong_induct) auto

lemma fresh_term_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_var by force
qed (auto simp: fresh_Cons)

lemma ty_valid_vars: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> ; Set.member (atom a) (fv_\<tau> \<tau>) \<rbrakk> \<Longrightarrow> BTyVar a \<in> \<Gamma>"
  by (nominal_induct \<Gamma> \<tau> avoiding: a rule: Ty.strong_induct) (auto simp: supp_at_base)

lemma ty_fresh_vars: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (nominal_induct \<Gamma> \<tau> avoiding: a rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_tyvar by force
next
  case (Ty_Forall a \<Gamma> \<sigma>)
  then show ?case by (metis \<tau>.fresh(4) binder.supp(2) fresh_Cons fresh_def list.set(1) list.simps(15) supp_at_base)
qed auto

lemma free_in_context_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; Set.member (atom x) (fv_term e) \<rbrakk> \<Longrightarrow> \<exists>\<tau>'. BVar x \<tau>' \<in> \<Gamma>"
proof(nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case by (metis atom_eq_iff singletonD supp_at_base term.fv_defs(1))
next
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then show ?case by (metis Diff_iff Un_iff fresh_at_base(2) fresh_def isin.simps(2) no_vars_in_ty term.fv_defs(5))
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then show ?case by (metis Diff_iff Un_iff fresh_at_base(2) fresh_def isin.simps(2) no_vars_in_ty term.fv_defs(7))
next
  case (T_AppTI \<Gamma> e a \<sigma> \<tau>)
  then show ?case using fresh_def by fastforce
qed auto

lemma fresh_subst_type_same: "atom a \<sharp> \<sigma> \<Longrightarrow> subst_type \<tau> a \<sigma> = \<sigma>"
proof (induction \<tau> a \<sigma> rule: subst_type.induct)
  case (4 b \<tau> a \<sigma>)
  then show ?case
    using fresh_Pair fresh_at_base(2) fresh_def list.set(1) list.set(2) subst_type.simps(4) by fastforce
qed auto

lemma fresh_term_tyvar: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: a rule: T.strong_induct)
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then show ?case using fresh_Cons ty_fresh_vars by fastforce
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then show ?case using fresh_Cons ty_fresh_vars by fastforce
next
  case (T_AppTI \<Gamma> e b \<sigma> \<tau>)
  have "atom a \<sharp> \<tau>" using T_AppTI.hyps(3) T_AppTI.prems ty_fresh_vars by blast
  then show ?case by (simp add: T_AppTI.hyps(2) T_AppTI.prems)
next
  case (T_AbsTI a \<Gamma> e \<sigma>)
  then show ?case by (metis binder.supp(2) fresh_Cons fresh_def list.set(1) list.simps(15) supp_at_base term.fresh(6))
qed auto

lemma context_invariance_ty:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>"
  and has_tyvars: "\<forall>a. Set.member (atom a) (fv_\<tau> \<tau>) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>"
using assms proof (nominal_induct \<Gamma> \<tau> avoiding: \<Gamma>' rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using supp_at_base Ty.Ty_Var by fastforce
qed (auto intro: Ty.intros)

theorem progress: "[] \<turnstile> e : \<tau> \<Longrightarrow> is_value e \<or> (\<exists>e'. Step e e')"
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
      then show ?thesis using ST_App2I \<open>is_value e1\<close> by blast
    qed
  next
    assume "\<exists>e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
next
  case (T_LetI e1 \<tau>1 x e2 \<tau>2)
  then show ?case using ST_SubstI ST_LetI by blast
next
  case (T_AppTI e a \<sigma> \<tau>)
  from T_AppTI(2) show ?case
  proof (elim disjE)
    assume "is_value e"
    then obtain b e1 where "e = (\<Lambda> b . e1)" using T_AppTI
      by (smt T.cases \<tau>.distinct(11) \<tau>.distinct(5) is_value.simps(1) is_value.simps(4) is_value.simps(5) is_value.simps(7))
    then show ?thesis using Step.ST_BetaTI T_AppTI by blast
  next
    assume "\<exists>e'. Step e e'"
    then show ?thesis using ST_AppTI by fast
  qed
qed auto

lemma T_Abs_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<exists>\<tau>2. BVar x \<tau>1#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<tau>1 \<rightarrow> \<tau>2) \<and> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1"
proof (cases rule: T.cases[OF a])
  case (3 x' \<Gamma>' \<tau>1' e' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" by (metis "3"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(5))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 3 swap by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 3 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using T.eqvt
      by (metis "3"(1) "3"(2) "3"(6) flip_def no_vars_in_ty swap_fresh_fresh term.eq_iff(5))

    have 4: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "1" "3"(1) "3"(4) Cons_eqvt a binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_Cons fresh_term_var term.fresh(5))

    from 1 2 3 4 swap show ?thesis by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  (*shows "\<exists>\<tau>1. \<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau> \<and> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1"*)
  shows "\<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau> \<and> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1"
proof (cases rule: T.cases[OF a])
  case (5 x' \<Gamma>' _ \<tau>1 e2' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e2' = e2"
    by (metis "5"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_flip_cancel permute_plus term.eq_iff(7))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 5 swap by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1 # \<Gamma>'" using b by (simp add: 5 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using T.eqvt by (metis "5"(1) "5"(3) "5"(6) flip_fresh_fresh no_vars_in_ty)
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "5"(1) "5"(4) Cons_eqvt b binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_PairD(1) no_vars_in_ty)

    from 2 3 5 swap show ?thesis by auto
  qed
qed simp_all

lemma T_AbsT_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<Lambda> a . e) : \<tau>" and b: "atom a \<sharp> \<Gamma>" "atom a \<sharp> \<tau>"
  shows "\<exists>\<sigma>. BTyVar a # \<Gamma> \<turnstile> e : \<sigma> \<and> \<tau> = (\<forall> a . \<sigma>)"
proof (cases rule: T.cases[OF a])
  case (7 a' \<Gamma>' e' \<sigma>')
  have swap: "(a \<leftrightarrow> a') \<bullet> e' = e" by (metis (no_types, lifting) "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(6))
  then have x: "BTyVar a # \<Gamma> \<turnstile> e : (a \<leftrightarrow> a') \<bullet> \<sigma>'" by (smt "7"(1) "7"(4) "7"(5) Cons_eqvt T.eqvt b binder.perm_simps(2) flip_at_simps(2) flip_def fresh_PairD(2) swap_fresh_fresh)
  have "\<tau> = (\<forall>a . (a \<leftrightarrow> a') \<bullet> \<sigma>')"
    by (metis "7"(3) "7"(5) Ty_Forall Ty_Var \<tau>.fresh(2) \<tau>.fresh(4) \<tau>.perm_simps(4) b(2) binder.fresh(2) flip_at_simps(2) flip_fresh_fresh fresh_Cons fresh_PairD(2) fresh_not_isin_tyvar isin.simps(5) ty_fresh_vars)
  then show ?thesis using x by blast
qed simp_all

lemma fv_supp_subset: "fv_\<tau> \<tau> \<subseteq> supp \<tau>"
  by (induction \<tau> rule: \<tau>.induct) (auto simp: \<tau>.supp)

lemma context_invariance:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  and has_vars: "\<forall>x \<tau>'. Set.member (atom x) (fv_term e) \<and> BVar x \<tau>' \<in> \<Gamma> \<longrightarrow> BVar x \<tau>' \<in> \<Gamma>'"
  and has_tyvars: "\<forall>a. Set.member (atom a) (fv_term e) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile> e : \<tau>"
using assms proof (nominal_induct \<Gamma> e \<tau> avoiding: \<Gamma>' rule: T.strong_induct)
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then have 1: "BVar x \<tau>1 # \<Gamma>' \<turnstile> e : \<tau>2" by auto
  have 2: "\<forall>a. (\<in>) (atom a) (fv_\<tau> \<tau>1) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'" using T_AbsI(7) fv_supp_subset by auto
  have 3: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1" using context_invariance_ty[OF T_AbsI(3) 2] .
  show ?case using T.T_AbsI[OF T_AbsI(1) 3 1] .
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case by (metis T.T_AppI Un_iff term.fv_defs(2))
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then have 1: "BVar x \<tau>1 # \<Gamma>' \<turnstile> e2 : \<tau>2" by auto
  from T_LetI have 2: "atom x \<sharp> (\<Gamma>', e1)" by auto
  from T_LetI have 3: "\<Gamma>' \<turnstile> e1 : \<tau>1" by force
  have 4: "\<forall>a. (\<in>) (atom a) (fv_\<tau> \<tau>1) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'" using T_LetI(10) fv_supp_subset by auto
  have 5: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1" using context_invariance_ty[OF T_LetI(4) 4] .
  show ?case using T.T_LetI[OF 2 5 1 3] .
next
  case (T_AppTI \<Gamma> e a \<sigma> \<tau>)
  then have 1: "\<Gamma>' \<turnstile> e : \<forall> a . \<sigma>" by simp
  have 2: "\<forall>a. (\<in>) (atom a) (fv_\<tau> \<tau>) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'" using fv_supp_subset T_AppTI(5) by auto
  have 3: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>" using context_invariance_ty[OF T_AppTI(3) 2] .
  show ?case using T.T_AppTI[OF 1 3] .
next
  case (T_AbsTI a \<Gamma> e \<sigma>)
  then have 1: "BTyVar a # \<Gamma>' \<turnstile> e : \<sigma>" by auto
  have 2: "atom a \<sharp> \<Gamma>'" using T_AbsTI by auto
  show ?case using T.T_AbsTI[OF 1 2] .
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
  have 2: "\<Gamma> \<turnstile> subst_term v x e1 : (\<tau>1 \<rightarrow> \<tau>)" using App(1)[OF 1(1) App(4)] .
  have 3: "\<Gamma> \<turnstile> subst_term v x e2 : \<tau>1" using App(2)[OF 1(2) App(4)] .
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
  obtain \<tau>2 where P: "BVar y \<sigma> # BVar x \<tau>' # \<Gamma> \<turnstile> e' : \<tau>2 \<and> \<tau> = (\<sigma> \<rightarrow> \<tau>2) \<and> BVar x \<tau>' # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma>" using T_Abs_Inv[OF Lam(7) 1] by blast
  then have 2: "BVar x \<tau>' # BVar y \<sigma> # \<Gamma> \<turnstile> e' : \<tau>2" using Lam(4) context_invariance by auto
  have 3: "BVar y \<sigma> # \<Gamma> \<turnstile> subst_term v x e' : \<tau>2" using Lam(6)[OF 2 Lam(8)] .
  from P have 4: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma>" using context_invariance_ty by auto
  from Lam have 5: "atom y \<sharp> (x, v)" by auto
  show ?case using T.T_AbsI[OF Lam(1) 4 3] subst_term.simps(2)[OF 5] P by auto
next
  case (TyLam a e)
  have 1: "atom a \<sharp> BVar x \<tau>' # \<Gamma>" by (simp add: TyLam.hyps(1) TyLam.hyps(5) fresh_Cons)
  obtain \<sigma> where P: "BTyVar a # BVar x \<tau>' # \<Gamma> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a . \<sigma>)" using T_AbsT_Inv[OF TyLam(7) 1 TyLam(2)] by blast
  then have 1: "BVar x \<tau>' # BTyVar a # \<Gamma> \<turnstile> e : \<sigma>" using context_invariance by fastforce
  have 2: "BTyVar a # \<Gamma> \<turnstile> subst_term v x e : \<sigma>" using TyLam(6)[OF 1 TyLam(8)] .
  have 3: "atom a \<sharp> \<Gamma>" using fresh_subst_term[OF TyLam(3)] TyLam(1) by auto
  have 4: "atom a \<sharp> (x, v)" using TyLam by auto
  show ?case using T.T_AbsTI[OF 2 3] P subst_term.simps(3)[OF 4] by auto
next
  case (Let y \<tau>1 e1 e2)
  then have 1: "atom y \<sharp> BVar x \<tau>' # \<Gamma>" by (simp add: fresh_Cons)
  have P: "BVar x \<tau>' # \<Gamma> \<turnstile> e1 : \<tau>1" "BVar y \<tau>1 # BVar x \<tau>' # \<Gamma> \<turnstile> e2 : \<tau>" "BVar x \<tau>' # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1" using T_Let_Inv[OF Let(8) 1] by auto
  have 2: "\<Gamma> \<turnstile> subst_term v x e1 : \<tau>1" using Let(6)[OF P(1) Let(9)] .
  have 3: "BVar x \<tau>' # BVar y \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>" using Let(4) P(2) context_invariance by auto
  have 4: "BVar y \<tau>1 # \<Gamma> \<turnstile> subst_term v x e2 : \<tau>" using Let(7)[OF 3 Let(9)] .
  have 5: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1" using context_invariance_ty[OF P(3)] by auto
  have "atom y \<sharp> subst_term v x e1" using "2" Let(1) fresh_term_var by blast
  then have 6: "atom y \<sharp> (\<Gamma>, subst_term v x e1)" using Let(1) by auto
  show ?case using T.T_LetI[OF 6 5 4 2] Let by auto
qed

lemma subst_type_order: "\<lbrakk> atom a \<sharp> b ; atom b \<sharp> \<tau>' ; atom a \<sharp> \<tau> \<rbrakk> \<Longrightarrow> subst_type \<tau> b (subst_type \<tau>' a \<sigma>') = subst_type \<tau>' a (subst_type \<tau> b \<sigma>')"
proof (nominal_induct \<sigma>' avoiding: a b \<tau> \<tau>' rule: \<tau>.strong_induct)
  case (TyVar x)
  then show ?case by (metis \<tau>.fresh(2) fresh_subst_type_same subst_type.simps(2))
qed auto

lemma subst_type_order_2: "\<lbrakk> atom b \<sharp> \<tau>' ; atom b \<sharp> a \<rbrakk> \<Longrightarrow> subst_type \<tau>' a (subst_type \<tau> b \<sigma>') = subst_type (subst_type \<tau>' a \<tau>) b (subst_type \<tau>' a \<sigma>')"
proof (nominal_induct \<sigma>' avoiding: a b \<tau> \<tau>' rule: \<tau>.strong_induct)
  case (TyVar x)
  then show ?case using fresh_at_base(2) fresh_subst_type_same by auto
qed (auto simp: fresh_subst_type)

lemma subst_type_ty: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau>"
proof (nominal_induct \<tau> avoiding: a \<Gamma> \<tau>' rule: \<tau>.strong_induct)
  case (TyVar x)
  then show ?case by (metis \<tau>.fv_defs(2) atom_eq_iff context_invariance_ty empty_iff insertE isin.simps(5) subst_type.simps(2) supp_at_base)
next
  case (TyArrow e1 e2)
  then show ?case by (metis Ty.simps \<tau>.distinct(11) \<tau>.distinct(3) \<tau>.distinct(7) \<tau>.eq_iff(3) subst_type.simps(3))
next
  case (TyForall b \<tau>)
  have "BTyVar b # BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>" proof (cases rule: Ty.cases[OF TyForall(5)])
    case (4 c \<Gamma> \<sigma>)
    then have "\<tau> = (b \<leftrightarrow> c) \<bullet> \<sigma>" by (metis Abs1_eq_iff(3) TyForall.prems(1) \<tau>.eq_iff(4) \<tau>.perm_simps(4) flip_at_simps(2) flip_fresh_fresh ty_fresh_vars)
    then show ?thesis
      by (smt "4"(1) "4"(3) "4"(4) Cons_eqvt Ty.eqvt TyForall.hyps(1) TyForall.hyps(2) binder.fresh(2) binder.perm_simps(2) flip_at_simps(2) flip_def fresh_Cons swap_fresh_fresh)
  qed auto
  then have 1: "BTyVar a # BTyVar b # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>" using context_invariance_ty by auto
  show ?case
    by (metis (mono_tags, lifting) "1" Ty.simps TyForall.hyps(1) TyForall.hyps(2) TyForall.hyps(3) TyForall.hyps(4) TyForall.prems(2) TyForall.prems(3) binder.supp(2) context_invariance_ty fresh_Cons fresh_Pair fresh_def isin.simps(5) singletonD subst_type.simps(4) supp_at_base)
qed (auto intro: Ty.intros)


lemma type_substitution: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile> e : \<sigma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>' ; \<forall>b. BTyVar b \<in> \<Gamma> \<longrightarrow> BTyVar b \<in> \<Gamma>' ; \<forall>x \<tau>. BVar x \<tau> \<in> \<Gamma> \<longrightarrow> BVar x (subst_type \<tau>' a \<tau>) \<in> \<Gamma>' ; atom a \<sharp> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<sigma>"
proof (nominal_induct e avoiding: a \<Gamma> \<Gamma>' \<sigma> \<tau>' rule: term.strong_induct)
  case (Var x)
  then have 1: "BVar x (subst_type \<tau>' a \<sigma>) \<in> \<Gamma>'"
    by (smt T.cases isin.simps(3) term.distinct(1) term.distinct(11) term.distinct(3) term.distinct(5) term.distinct(7) term.distinct(9) term.eq_iff(1))
  show ?case using T.T_VarI[OF 1] by simp
next
  case (App e1 e2)
  obtain \<tau>1 where "BTyVar a # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<sigma>) \<and> BTyVar a # \<Gamma> \<turnstile> e2 : \<tau>1" using T.cases[OF App(3)] by fastforce
  then have P: "BTyVar a # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<sigma>)" "BTyVar a # \<Gamma> \<turnstile> e2 : \<tau>1" by auto

  have 1: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e1 : subst_type \<tau>' a \<tau>1 \<rightarrow> subst_type \<tau>' a \<sigma>" using App(1)[OF P(1) App(4) App(5) App(6) App(7)] by simp
  have 2: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e2 : subst_type \<tau>' a \<tau>1" by (rule App(2)[OF P(2) App(4) App(5) App(6) App(7)])

  then show ?case using T.T_AppI[OF 1 2] by simp
next
  case (TyApp e \<tau>)

  have "\<exists>b \<sigma>'. BTyVar a # \<Gamma> \<turnstile> e : (\<forall>b . \<sigma>') \<and> atom b \<sharp> a \<and> \<sigma> = subst_type \<tau> b \<sigma>' \<and> atom b \<sharp> \<tau>' \<and> BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>"
  proof (cases rule: T.cases[OF TyApp(2)])
    case (6 \<Gamma>2 t b \<sigma>2 \<tau>2)
    then have 1: "BTyVar a # \<Gamma> \<turnstile> e : \<forall> b . \<sigma>2" "\<sigma> = subst_type \<tau> b \<sigma>2" "BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>" by auto
    obtain c::tyvar where "atom c \<sharp> (a, b, \<sigma>2, \<tau>')" using obtain_fresh by blast
    then have c: "atom c \<sharp> b" "atom c \<sharp> \<sigma>2" "atom c \<sharp> a" "atom c \<sharp> \<tau>'" using fresh_Pair by auto
    from 1(1) have 2: "BTyVar a # \<Gamma> \<turnstile> e : \<forall> c . (b \<leftrightarrow> c) \<bullet> \<sigma>2" by (smt Abs1_eq_iff(3) \<tau>.eq_iff(4) c(1) c(2) flip_commute fresh_at_base(2))
    from 1(2) have "\<sigma> = subst_type \<tau> c ((b \<leftrightarrow> c) \<bullet> \<sigma>2)" using subst_type_var_name c by auto
    then show ?thesis using 2 c(3) c(4) 1(3) by blast
  qed auto
  then obtain b \<sigma>' where P: "BTyVar a # \<Gamma> \<turnstile> e : (\<forall>b . \<sigma>')" "atom b \<sharp> a" "\<sigma> = subst_type \<tau> b \<sigma>'" "atom b \<sharp> \<tau>'" "BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>" by blast

  have 1: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>'" using context_invariance_ty[OF TyApp(3)] using TyApp(5) TyApp.prems(3) by blast
  have 2: "BTyVar a # \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>" using context_invariance_ty[OF P(5)] by (smt TyApp.prems(3) isin.simps(5))
  have 3: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau>" using subst_type_ty[OF 2 1 TyApp(6)] .
  have 4: "\<Gamma>' \<turnstile> subst_term_type \<tau>' a e : \<forall> b . subst_type \<tau>' a \<sigma>'" using TyApp(1)[OF P(1) TyApp(3) TyApp(4) TyApp(5) TyApp(6)] P(2) P(4) by auto

  have "\<Gamma>' \<turnstile> TyApp (subst_term_type \<tau>' a e) (subst_type \<tau>' a \<tau>) : subst_type \<tau>' a (subst_type \<tau> b \<sigma>')" using T.T_AppTI[OF 4 3] subst_type_order_2[OF P(4) P(2)] by simp
  then show ?case using P(3) by simp
next
  case Unit
  then have "\<sigma> = TyUnit" using T.cases by fastforce
  then show ?case using T.T_UnitI by simp
next
  case (Lam x \<tau>1 e)
  then have 1: "atom x \<sharp> BTyVar a # \<Gamma>" by (simp add: fresh_Cons)
  obtain \<tau>2 where P: "BVar x \<tau>1 # BTyVar a # \<Gamma> \<turnstile> e : \<tau>2" "\<sigma> = (\<tau>1 \<rightarrow> \<tau>2)" "BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1" using T_Abs_Inv[OF Lam(7) 1] by blast
  then have 2: "BTyVar a # BVar x \<tau>1 # \<Gamma> \<turnstile> e : \<tau>2" using context_invariance[OF P(1)] by simp
  have 3: "BTyVar a # \<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1" using context_invariance_ty[OF P(3)] by (smt Lam.prems(3) isin.simps(5))
  have 4: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>'" using context_invariance_ty[OF Lam(8)] using Lam.prems(3) by blast
  have 5: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau>1" by (simp add: "3" "4" Lam.prems(5) subst_type_ty)
  have 6: "BVar x \<tau>1 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>'" using context_invariance_ty[OF Lam(8)] Lam(9) by auto

  from 4 have 7: "atom a \<sharp> \<tau>'" using Lam.prems(5) ty_fresh_vars by blast
  have 8: "atom a \<sharp> BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>'" using "5" Lam.prems(5) fresh_Cons ty_fresh_vars by fastforce

  have 9: "BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>2" using Lam(6)[OF 2 6 _ _ 8] by (simp add: Lam.prems(3) Lam.prems(4))

  have "\<Gamma>' \<turnstile> \<lambda>x : subst_type \<tau>' a \<tau>1 . subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>1 \<rightarrow> subst_type \<tau>' a \<tau>2" using T.T_AbsI[OF Lam(3) 5 9] .
  then show ?case using P(2) by simp
next
  case (TyLam b e)
  then have 1: "atom b \<sharp> BTyVar a # \<Gamma>" by (simp add: fresh_Cons)
  obtain \<tau> where P: "BTyVar b # BTyVar a # \<Gamma> \<turnstile> e : \<tau>" "\<sigma> = (\<forall> b . \<tau>)" using T_AbsT_Inv[OF TyLam(7) 1 TyLam(4)] by blast
  then have 2: "subst_type \<tau>' a \<sigma> = (\<forall> b . subst_type \<tau>' a \<tau>)" by (simp add: TyLam(1) TyLam(5))
  have 3: "BTyVar a # BTyVar b # \<Gamma> \<turnstile> e : \<tau>" using context_invariance[OF P(1)] TyLam(9) TyLam(10) by auto
  have 4: "BTyVar b # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>'" using context_invariance_ty[OF TyLam(8)] by simp
  have 5: "atom a \<sharp> BTyVar b # \<Gamma>'" using TyLam(1) TyLam.prems(5) fresh_Cons by fastforce

  have 9: "BTyVar b # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<tau>" using TyLam(6)[OF 3 4 _ _ 5] TyLam(9) TyLam(10) by simp

  show ?case using T.T_AbsTI[OF 9 TyLam(3)] 2 TyLam(1) TyLam(5) by simp
next
  case (Let x \<tau>1 e1 e2)
  then have 1: "atom x \<sharp> BTyVar a # \<Gamma>" by (simp add: fresh_Cons)
  have P: "BTyVar a # \<Gamma> \<turnstile> e1 : \<tau>1" "BVar x \<tau>1 # BTyVar a # \<Gamma> \<turnstile> e2 : \<sigma>" "BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1" using T_Let_Inv[OF Let(8) 1] by auto
  have 2: "atom x \<sharp> e1" using "1" P(1) fresh_term_var by blast
  have "atom x \<sharp> subst_term_type \<tau>' a e1" using fresh_subst_term_type[OF Let(5) 2] .
  then have 3: "atom x \<sharp> (\<Gamma>', subst_term_type \<tau>' a e1)" using Let(3) by simp
  have 4: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y subst_type \<tau>' a \<tau>1" using Let.prems(2) Let.prems(3) Let.prems(5) P(3) context_invariance_ty isin.simps(5) subst_type_ty by presburger
  have 5: "atom a \<sharp> BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>'" using "4" Let.prems(5) fresh_Cons ty_fresh_vars by fastforce
  have 6: "BTyVar a # BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<sigma>" using context_invariance[OF P(2)] by auto
  have 7: "BVar x \<tau>1 # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>'" using Let.prems(2) context_invariance_ty isin.simps(4) by blast

  have 9: "BVar x (subst_type \<tau>' a \<tau>1) # \<Gamma>' \<turnstile> subst_term_type \<tau>' a e2 : subst_type \<tau>' a \<sigma>" using Let(7)[OF 6 7 _ _ 5] Let(10) Let(11) by simp
  show ?case using T.T_LetI[OF 3 4 9] using Let P(1) by auto
qed

theorem preservation: "\<lbrakk> [] \<turnstile> e : \<tau> ; Step e e' \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
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
  next
    case (ST_App2I e2)
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
      then show ?thesis by (metis T_LetI.hyps(4) T_LetI.hyps(5) local.ST_SubstI(1) local.ST_SubstI(2) subst_term_det substitution)
    next
      case False
      then have 1: "atom y \<sharp> [(x, \<tau>1)]" by (simp add: fresh_Cons fresh_Nil)
      have "(x \<leftrightarrow> y) \<bullet> e2 = e" by (metis Abs1_eq_iff'(3) False flip_commute local.ST_SubstI(1))
      then have "[BVar y \<tau>1] \<turnstile> e : \<tau>2" using T.eqvt by (metis T_AbsI T_Abs_Inv T_LetI.hyps(3) T_LetI.hyps(4) \<tau>.eq_iff(3) fresh_Nil local.ST_SubstI(1) term.eq_iff(5))
      then show ?thesis using T_LetI ST_SubstI substitution by auto
    qed
  next
    case (ST_LetI e1' x' e2')

    have "atom x' \<sharp> e1'" using T_LetI.hyps(6) fresh_Nil fresh_term_var local.ST_LetI(3) by blast
    then have 1: "atom x' \<sharp> ([], e1')" using fresh_Pair fresh_Nil by auto

    have swap: "(x \<leftrightarrow> x') \<bullet> e2' = e2"
      by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def local.ST_LetI(1) permute_flip_cancel permute_plus)

    have "(x \<leftrightarrow> x') \<bullet> ([BVar x \<tau>1] \<turnstile> e2 : \<tau>2)" by (simp add: T_LetI.hyps(4))
    then have "((x \<leftrightarrow> x') \<bullet> [BVar x \<tau>1]) \<turnstile> e2' : \<tau>2" by (metis (full_types) T.eqvt T_LetI.hyps(4) flip_commute flip_fresh_fresh local.swap no_vars_in_ty permute_flip_cancel2)
    then have 2: "[BVar x' \<tau>1] \<turnstile> e2' : \<tau>2" by (simp add: flip_fresh_fresh)
    have 3: "[] \<turnstile>\<^sub>t\<^sub>y \<tau>1" by (simp add: T_LetI.hyps(3))

    show ?thesis using ST_LetI(2) T.T_LetI[OF 1 3 2 T_LetI(6)[OF ST_LetI(3)]] by simp
  qed
next
  case (T_AppTI e a \<sigma> \<tau>)
  from T_AppTI(4) show ?case
  proof cases
    case (ST_BetaTI b t)
    obtain c::tyvar where "atom c \<sharp> (a, b, t, \<sigma>)" using obtain_fresh by blast
    then have c: "atom c \<sharp> a" "atom c \<sharp> b" "atom c \<sharp> t" "atom c \<sharp> \<sigma>" "atom c \<sharp> (b, t)" "atom c \<sharp> (a, \<sigma>)" using fresh_Pair by auto
    have 1: "[] \<turnstile> (\<Lambda> c . (b \<leftrightarrow> c) \<bullet> t) : \<forall> c . (a \<leftrightarrow> c) \<bullet> \<sigma>" by (smt Abs_lst_rename T_AppTI.hyps(1) \<tau>.eq_iff(4) atom_tyvar_sort c(3) c(4) local.ST_BetaTI(1) term.eq_iff(6))

    have 2: "[BTyVar c] \<turnstile> (b \<leftrightarrow> c) \<bullet> t : (a \<leftrightarrow> c) \<bullet> \<sigma>"
    proof (cases rule: T.cases[OF 1])
      case (7 a' \<Gamma> e \<sigma>')
      have 1: "(b \<leftrightarrow> c) \<bullet> t = (a' \<leftrightarrow> c) \<bullet> e"
        by (metis (no_types, lifting) "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_commute flip_def permute_flip_cancel2 permute_plus term.eq_iff(6))
      have 2: "(a \<leftrightarrow> c) \<bullet> \<sigma> = (a' \<leftrightarrow> c) \<bullet> \<sigma>'"
        by (smt "7"(3) Abs1_eq_iff(3) Abs_lst_rename Nominal2_Base.swap_self \<tau>.eq_iff(4) atom_tyvar_sort c(4) flip_def)
      show ?thesis using 7(4) 1 2 by (smt "7"(1) Cons_eqvt Nil_eqvt T.eqvt binder.perm_simps(2) flip_at_simps(1))
    qed auto

    have "[] \<turnstile> subst_term_type \<tau> c ((b \<leftrightarrow> c) \<bullet> t) : subst_type \<tau> c ((a \<leftrightarrow> c) \<bullet> \<sigma>)" using type_substitution[OF 2 T_AppTI(3) _ _ fresh_Nil] by simp
    then show ?thesis using ST_BetaTI(2) subst_term_type_var_name[OF c(5)] subst_type_var_name[OF c(6)] by presburger
  next
    case (ST_AppTI e2)
    then show ?thesis by (simp add: T.T_AppTI T_AppTI.hyps(2) T_AppTI.hyps(3))
  qed
next
  case (T_AbsTI a e \<sigma>)
  then show ?case using beta_nf_def is_value.simps(3) value_beta_nf by blast
qed

definition stuck :: "term \<Rightarrow> bool" where
  "stuck e \<equiv> \<not>is_value e \<and> beta_nf e"

inductive Steps :: "term \<Rightarrow> term \<Rightarrow> bool" (infix "\<longrightarrow>*" 70) where
  refl: "Steps e e"
| trans: "\<lbrakk> Steps e1 e2 ; Step e2 e3 \<rbrakk> \<Longrightarrow> Steps e1 e3"

lemma multi_preservation: "\<lbrakk> e \<longrightarrow>* e' ; [] \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
  by (induction e e' rule: Steps.induct) (auto simp: preservation)

corollary soundness: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow>* e' \<rbrakk> \<Longrightarrow> \<not>(stuck e')"
  unfolding stuck_def beta_nf_def
  using progress multi_preservation by blast

lemma beta_same[simp]: "\<lbrakk> e1 \<longrightarrow>* e1' ; beta_nf e1 \<rbrakk> \<Longrightarrow> e1 = e1'"
  by (induction e1 e1' rule: Steps.induct) (auto simp: beta_nf_def)

fun path :: "term \<Rightarrow> term list \<Rightarrow> term \<Rightarrow> bool" where
  "path a [] b \<longleftrightarrow> a = b \<or> Step a b"
| "path a (x#xs) b \<longleftrightarrow> Step a x \<and> path x xs b"

lemma path_snoc: "\<lbrakk> path a xs b ; Step b c \<rbrakk> \<Longrightarrow> path a (xs@[b]) c \<or> path a xs c"
  by (induction a xs b arbitrary: c rule: path.induct) auto

lemma Steps_concat: "\<lbrakk> e2 \<longrightarrow>* e3 ; e1 \<longrightarrow>* e2 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"
  apply (induction e2 e3 arbitrary: e1 rule: Steps.induct)
  using Steps.simps by blast+

lemma Steps_path: "a \<longrightarrow>* b \<longleftrightarrow> (\<exists>p. path a p b)"
proof
  assume "a \<longrightarrow>* b"
  then show "\<exists>p. path a p b"
  proof (induction a b rule: Steps.induct)
    case (refl e)
    then have "path e [] e" by simp
    then show ?case by blast
  next
    case (trans e1 e2 e3)
    then obtain xs where "path e1 xs e2" by blast
    then have "path e1 (xs@[e2]) e3 \<or> path e1 xs e3" using trans(2) path_snoc by simp
    then show ?case by blast
  qed
next
  assume "\<exists>p. path a p b"
  then obtain p where "path a p b" by blast
  then show "a \<longrightarrow>* b"
  proof (induction a p b rule: path.induct)
    case (1 a b)
    then show ?case using Steps.intros by auto
  next
    case (2 a x xs b)
    then have a: "a \<longrightarrow>* x" using Steps.intros by auto
    from 2 have b: "x \<longrightarrow>* b" by simp
    show ?case using Steps_concat[OF b a] .
  qed
qed

lemma Steps_fwd_induct[consumes 1, case_names refl trans]:
  assumes "a \<longrightarrow>* b"
    and "\<And>x. P x x" "\<And>x y z. y \<longrightarrow>* z \<Longrightarrow> P y z \<Longrightarrow> Step x y \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from assms(1) obtain p where P: "path a p b" using Steps_path by blast
  then show ?thesis
  proof (induction a p b rule: path.induct)
    case (1 a b)
    then show ?case
    proof (cases "a = b")
      case True
      then show ?thesis using assms(2) by simp
    next
      case False
      then have 1: "Step a b" using 1 by simp
      have 2: "b \<longrightarrow>* b" using Steps.refl by simp
      show ?thesis using assms(3)[OF 2 assms(2) 1] .
    qed
  next
    case (2 a x xs b)
    then have 1: "P x b" by simp
    from 2 have 3: "x \<longrightarrow>* b" using Steps_path by auto
    from 2 have 4: "Step a x" by simp
    show ?case using assms(3)[OF 3 1 4] .
  qed
qed

lemma beta_equivalence: "\<lbrakk> e1 \<longrightarrow>* e1' ; e2 \<longrightarrow>* e2' ; e1 = e2 ; beta_nf e1' ; beta_nf e2' \<rbrakk> \<Longrightarrow> e1' = e2'"
proof (induction e1 e1' arbitrary: e2 e2' rule: Steps_fwd_induct)
  case (refl x)
  then show ?case by simp
next
  case (trans x y z)
  then show ?case by (metis Steps.simps Steps_path beta_same path.elims(2) Step_deterministic)
qed

end