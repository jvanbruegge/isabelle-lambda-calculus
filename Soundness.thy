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

lemma context_invariance:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  and has_vars: "\<forall>x \<tau>'. Set.member (atom x) (fv_term e) \<and> BVar x \<tau>' \<in> \<Gamma> \<longrightarrow> BVar x \<tau>' \<in> \<Gamma>'"
  and has_tyvars: "\<forall>a. Set.member (atom a) (fv_\<tau> \<tau>) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile> e : \<tau>"
using assms proof(nominal_induct \<Gamma> e \<tau> avoiding: \<Gamma>' rule: T.strong_induct)
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  from T_AppI(1) have "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1" sorry

  have 1: "\<forall>a. (\<in>) (atom a) (fv_\<tau> (\<tau>1 \<rightarrow> \<tau>2)) \<and> BTyVar a \<in> \<Gamma>" sorry
  then have "\<Gamma>' \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>2" using T_AppI(1) T_AppI(2) T_AppI(5) by (meson fresh_not_isin_tyvar obtain_fresh) 
  then show ?case using 1 fresh_not_isin_tyvar obtain_fresh by blast
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then have 1: "\<Gamma>' \<turnstile> e1 : \<tau>1" by auto
  from T_LetI have 2: "BVar x \<tau>1#\<Gamma>' \<turnstile> e2 : \<tau>2" by auto
  from T_LetI have 3: "atom x \<sharp> (\<Gamma>', e1)" by force
  from T_LetI have 4: "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>1" sorry
  show ?case using T.T_LetI[OF 3 _ 2 1] .
next
  case (T_AbsTI a \<Gamma> e \<sigma>)
  then have 1: "BTyVar a # \<Gamma>' \<turnstile> e : \<sigma>" by simp
  from T_AbsTI have 2: "atom a \<sharp> (e, \<Gamma>')" by simp
  show ?case using T.T_AbsTI[OF 1 2] .
qed (auto simp: T.intros supp_at_base)


lemma context_invariance_ty:
  assumes "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>"
  and has_tyvars: "\<forall>a. Set.member (atom a) (fv_\<tau> \<tau>) \<and> BTyVar a \<in> \<Gamma> \<longrightarrow> BTyVar a \<in> \<Gamma>'"
  shows "\<Gamma>' \<turnstile>\<^sub>t\<^sub>y \<tau>"
using assms proof (nominal_induct \<Gamma> \<tau> avoiding: \<Gamma>' rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using supp_at_base Ty.Ty_Var by fastforce
qed (auto intro: Ty.intros)

lemma fresh_term_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_VarI y \<tau> \<Gamma>)
  then show ?case using T.T_VarI free_in_context fresh_def fresh_not_isin_var term.fv_defs(1) term.supp(1) by blast
qed (auto simp: fresh_Cons)

lemma fresh_term_tyvar: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: a rule: T.strong_induct)
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then show ?case sorry
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then show ?case sorry
next
  case (T_AppTI \<Gamma> e a \<sigma> \<tau>)
  then show ?case sorry
next
  case (T_AbsTI a \<Gamma> e \<sigma>)
  then show ?case sorry
qed auto


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
  shows "\<exists>\<tau>2. BVar x \<tau>1#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<tau>1 \<rightarrow> \<tau>2)"
proof (cases rule: T.cases[OF a])
  case (3 x' \<Gamma>' \<tau>1' e' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" by (metis "3"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(5))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis sorry
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 3 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using T.eqvt
      sorry

    have 4: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "1" "3"(1) "3"(4) Cons_eqvt a binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_Cons fresh_term_var term.fresh(5))

    from 1 2 3 4 swap show ?thesis by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> \<turnstile> Let x e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<exists>\<tau>1. \<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1#\<Gamma> \<turnstile> e2 : \<tau>"
proof (cases rule: T.cases[OF a])
  case (5 x' \<Gamma>' _ \<tau>1 e2' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e2' = e2"
    by (metis "5"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_flip_cancel permute_plus term.eq_iff(7))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis by (metis "5"(1) "5"(2) "5"(3) "5"(5) "5"(6) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(7))
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1 # \<Gamma>'" using b by (simp add: 5 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using T.eqvt by (metis "5"(1) "5"(3) "5"(5) flip_fresh_fresh no_vars_in_ty)
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "5"(1) "5"(4) Cons_eqvt b binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_PairD(1) no_vars_in_ty)

    from 2 3 5 swap show ?thesis by auto
  qed
qed simp_all

lemma substitution: "\<lbrakk> BVar x \<tau>'#\<Gamma> \<turnstile> e : \<tau> ; [] \<turnstile> v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> subst_term v x e : \<tau>"
proof (nominal_induct e avoiding: \<Gamma> \<tau> v x \<tau>' rule: term.strong_induct)
  case (Var y)
  then show ?case
  proof (cases "x = y")
    case True
    then have "\<tau> = \<tau>'" using Var T.cases by fastforce
    then show ?thesis using True Var context_invariance by fastforce
  next
    case False
    then show ?thesis using Var context_invariance
      by (metis (no_types, lifting) Rep_var_inverse atom_var_def subst_term.simps(1) isin.simps(2) singletonD supp_at_base term.fv_defs(1))
  qed
next
  case (Lam y \<sigma> e)
  then obtain \<tau>2 where P: "BVar y \<sigma>#BVar x \<tau>'#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<sigma> \<rightarrow> \<tau>2)" using T_Abs_Inv[OF Lam(7)] fresh_Cons fresh_Pair binder.fresh(1) by blast
  then have "BVar x \<tau>'#BVar y \<sigma>#\<Gamma> \<turnstile> e : \<tau>2" using context_invariance \<open>atom y \<sharp> x\<close> by auto
  then show ?case using Lam T_AbsI P by simp
next
  case (App e1 e2)
  obtain \<tau>1 where P: "(BVar x \<tau>' # \<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>) \<and> (BVar x \<tau>' # \<Gamma> \<turnstile> e2 : \<tau>1)" using T.cases[OF App(3)] by fastforce
  then show ?case using T_AppI App by fastforce
next
  case Unit
  then show ?case using T.cases[OF Unit(1)] T_UnitI by auto
next
  case (Let y e1 e2)
  have "atom y \<sharp> e1" using Let.hyps(1) Let.hyps(4) Let.hyps(5) Let.prems(1) T_Let_Inv binder.fresh(1) fresh_Cons fresh_term_var by blast
  then have "atom y \<sharp> subst_term v x e1" by (simp add: Let.hyps(3) fresh_subst_term) 
  then have 0: "atom y \<sharp> (\<Gamma>, subst_term v x e1)" using Let fresh_Pair by simp

  obtain \<tau>1 where P: "BVar x \<tau>'#\<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar y \<tau>1#BVar x \<tau>'#\<Gamma> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let(8)] Let fresh_Cons fresh_Pair binder.fresh(1) by blast
  then have 1: "BVar x \<tau>'#BVar y \<tau>1#\<Gamma> \<turnstile> e2 : \<tau>" using context_invariance Let(4) by force
  from P have 2: "BVar x \<tau>'#\<Gamma> \<turnstile> e1 : \<tau>1" by simp

  have 3: "\<Gamma> \<turnstile> subst_term v x e1 : \<tau>1" using Let(6)[OF 2 Let(9)] .
  have 4: "BVar y \<tau>1#\<Gamma> \<turnstile> subst_term v x e2 : \<tau>" using Let(7)[OF 1 Let(9)] .

  show ?case using T_LetI[OF 0 4 3] using Let by simp
next
  case (TyApp e \<tau>)
  then show ?case
    by (smt T.cases T_AppTI subst_term.simps(5) term.distinct(13) term.distinct(23) term.distinct(25) term.distinct(27) term.distinct(29) term.distinct(3) term.eq_iff(3))
next
  case (TyLam a e)

  have "\<exists>\<sigma>. \<tau> = (\<forall>a. \<sigma>)" apply (cases rule: T.cases[OF TyLam(7)]) apply auto[6]
      by (metis TyLam.hyps(2) \<tau>.fresh(4) \<tau>.perm_simps(4) flip_at_simps(2) flip_fresh_fresh fresh_at_base(2) fresh_def list.set(1) list.simps(15) supp_at_base)

  then obtain \<sigma> where P: "\<tau> = (\<forall>a. \<sigma>)" by blast
  then have e: "BVar x \<tau>' # BTyVar a # \<Gamma> \<turnstile> e : \<sigma>"
  proof (cases rule: T.cases[OF TyLam(7)])
    case (7 b \<Gamma>' e' \<sigma>')
    have 1: "(a \<leftrightarrow> b) \<bullet> e' = e" by (metis "7"(2) "7"(5) Abs1_eq_iff(3) flip_fresh_fresh fresh_PairD(1) term.eq_iff(6))
    have 2: "(a \<leftrightarrow> b) \<bullet> \<sigma>' = \<sigma>" by (metis "7"(3) Abs1_eq_iff(3) P TyLam.hyps(2) \<tau>.eq_iff(4) \<tau>.perm_simps(4) flip_at_simps(2) flip_fresh_fresh)

    from 7 have "BVar x \<tau>' # BTyVar b # \<Gamma> \<turnstile> e' : \<sigma>'" using context_invariance by auto
    then have "(a \<leftrightarrow> b) \<bullet> (BVar x \<tau>' # BTyVar b # \<Gamma> \<turnstile> e' : \<sigma>')" by simp
    then have 3: "((a \<leftrightarrow> b) \<bullet> BVar x \<tau>') # (BTyVar a) # ((a \<leftrightarrow> b) \<bullet> \<Gamma>) \<turnstile> e : \<sigma>" using 1 2 by auto

    have x: "atom a \<sharp> BVar x \<tau>'" by (simp add: TyLam)
    have "atom b \<sharp> BVar x \<tau>'" using 7(1) 7(5) fresh_Pair fresh_Cons TyLam by metis
    then have 4: "BVar x \<tau>' # (BTyVar a) # ((a \<leftrightarrow> b) \<bullet> \<Gamma>) \<turnstile> e : \<sigma>" using 3 flip_fresh_fresh[OF x] by metis

    have "atom b \<sharp> \<Gamma>" using 7(1) 7(5) fresh_Pair fresh_Cons by metis
    then show ?thesis using 4 flip_fresh_fresh[OF TyLam(1)] by auto
  qed auto

  have "atom a \<sharp> e"
    by (smt Abs1_eq_iff(3) P T.cases TyLam.prems(1) \<tau>.distinct(11) flip_fresh_fresh fresh_PairD(1) term.distinct(19) term.distinct(27) term.distinct(33) term.distinct(41) term.distinct(9) term.eq_iff(6))
  then have fresh: "atom a \<sharp> (subst_term v x e, \<Gamma>)" using fresh_subst_term[OF TyLam(3)] TyLam(1) by force

  show ?case using T.T_AbsTI[OF TyLam(6)[OF e TyLam(8)] fresh] P TyLam by force
qed

lemma type_fresh_in_context: "\<lbrakk> BVar x \<tau> \<in> \<Gamma> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (induction \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons b \<Gamma>)
  then show ?case
    apply (cases b rule: binder.exhaust)
    apply (metis binder.fresh(1) fresh_Cons isin.simps(2))
    using Cons.IH Cons.prems(1) Cons.prems(2) fresh_Cons isin.simps(3) by blast 
qed

lemma fresh_subst_type: "atom a \<sharp> \<sigma> \<Longrightarrow> subst_type \<tau> a \<sigma> = \<sigma>"
proof (induction \<tau> a \<sigma> rule: subst_type.induct)
  case (4 b \<tau> a \<sigma>)
  then show ?case
    using fresh_Pair fresh_at_base(2) fresh_def list.set(1) list.set(2) subst_type.simps(4) by fastforce
qed auto

lemma type_substitution: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile> e : \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> subst_term_type \<tau>' a e : subst_type \<tau>' a \<sigma>"
proof (nominal_induct e avoiding: a \<Gamma> \<sigma> \<tau>' rule: term.strong_induct)
  case (Var x)
  then have 1: "BVar x \<sigma> \<in> \<Gamma>" using T.cases by fastforce
  have 2: "atom a \<sharp> \<sigma>" using type_fresh_in_context[OF 1 Var(2)] .
  have "subst_type \<tau>' a \<sigma> = \<sigma>" using fresh_subst_type[OF 2, of \<tau>'] .
  then show ?case by (simp add: 1 T_VarI)
next
  case (App e1 e2)
  obtain \<tau>1 where 1: "BTyVar a # \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<sigma>) \<and> BTyVar a # \<Gamma> \<turnstile> e2 : \<tau>1" using T.cases[OF App(3)] by fastforce
  then show ?case using App.hyps(1) App.hyps(2) App.prems(2) T_AppI by fastforce
next
  case (TyApp e \<tau>)
  obtain b \<sigma>' where "BTyVar a # \<Gamma> \<turnstile> e : (\<forall>b . \<sigma>')" using T.cases[OF TyApp(2)] by fastforce
  then show ?case by (meson T_AppTI \<tau>.fresh(2) fresh_at_base(2) fresh_term_tyvar obtain_fresh term.fresh(3))
next
  case Unit
  then have "\<sigma> = TyUnit" by (cases rule: T.cases)
  then show ?case by (simp add: T_UnitI) 
next
  case (Lam x \<tau> e)
  obtain \<tau>2 where P: "\<sigma> = (\<tau> \<rightarrow> \<tau>2)" using Lam.hyps(1) Lam.hyps(2) Lam.prems(1) T_Abs_Inv binder.fresh(2) fresh_Cons by blast 
  then have 1: "BTyVar a # BVar x \<tau> # \<Gamma> \<turnstile> e : \<tau>2" by (metis Lam.hyps(2) Lam.prems(1) T_Abs_Inv \<tau>.eq_iff(3) context_invariance isin.simps(3))

  have "atom a \<sharp> \<tau>" using fresh_term_tyvar[OF Lam(6)] sorry
  then have "atom a \<sharp> BVar x \<tau>" by simp
  then have 2: "atom a \<sharp> BVar x \<tau> # \<Gamma>" using Lam.prems(2) fresh_Cons by blast 

  show ?case using Lam(5)[OF 1 2]
    by (metis "2" Lam.hyps(1) Lam.hyps(2) Lam.hyps(4) P T_AbsI binder.fresh(1) fresh_Cons fresh_Pair fresh_subst_type subst_term_type.simps(3) subst_type.simps(3))
next
  case (TyLam b e)
  have "\<exists>\<tau>. \<sigma> = (\<forall>b. \<tau>)" apply (cases rule: T.cases[OF TyLam(6)]) apply auto[6]
    by (metis TyLam(3) \<tau>.fresh(4) \<tau>.perm_simps(4) flip_at_simps(2) flip_fresh_fresh fresh_at_base(2) fresh_def list.set(1) list.set(2) supp_at_base)
  then obtain \<tau> where "\<sigma> = (\<forall>b. \<tau>)" by blast
  then have "BTyVar a # BTyVar b # \<Gamma> \<turnstile> e : \<tau>" using T.cases[OF TyLam(6)] sorry
  then show ?case sorry
next
case (Let x e1 e2)
  then show ?case sorry
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
  from \<open>Let x e1 e2 \<longrightarrow> e'\<close> show ?case
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
        by (smt Cons_eqvt T_LetI.hyps(3) binder.perm_simps(1) flip_at_simps(2) flip_commute flip_fresh_fresh fresh_Nil no_vars_in_ty) 
      then show ?thesis using T_LetI ST_SubstI substitution by auto
    qed
  next
    case (ST_LetI e1' x' e2')

    have "atom x' \<sharp> e1'" using T_LetI.hyps(5) fresh_Nil fresh_term_var local.ST_LetI(3) by blast 
    then have 1: "atom x' \<sharp> ([], e1')" using fresh_Pair fresh_Nil by auto

    have swap: "(x \<leftrightarrow> x') \<bullet> e2' = e2"
      by (metis Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def local.ST_LetI(1) permute_flip_cancel permute_plus)

    have "(x \<leftrightarrow> x') \<bullet> ([BVar x \<tau>1] \<turnstile> e2 : \<tau>2)" using T_LetI(3) by fastforce
    then have "((x \<leftrightarrow> x') \<bullet> [BVar x \<tau>1]) \<turnstile> e2' : \<tau>2"
      by (smt Cons_eqvt Nil_eqvt T_AbsI T_Abs_Inv T_LetI.hyps(1) T_LetI.hyps(3) \<tau>.eq_iff(3) atom_eqvt binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_eqvt fresh_term_var local.swap permute_flip_cancel term.perm_simps(5)) 
    then have 2: "[BVar x' \<tau>1] \<turnstile> e2' : \<tau>2" by (simp add: flip_fresh_fresh)

    show ?thesis using T.T_LetI[OF 1 2 T_LetI(5)[OF ST_LetI(3)]] ST_LetI(2) by simp
  qed
next
  case (T_AppTI e a \<sigma> \<tau>)
  from T_AppTI(3) show ?case
  proof cases
    case (ST_BetaTI b t)
    then show ?thesis
      by (smt T.cases T_AppTI.hyps(1) \<tau>.distinct(11) \<tau>.distinct(5) \<tau>.eq_iff(4) fresh_PairD(2) is_value.simps(3) is_value.simps(5) is_value.simps(7) isin.simps(1) subst_term_type_det subst_type_det term.distinct(20) term.eq_iff(6) type_substitution)
  next
    case (ST_AppTI e2)
    then show ?thesis by (simp add: T.T_AppTI T_AppTI.hyps(2))
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