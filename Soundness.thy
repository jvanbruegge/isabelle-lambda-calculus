theory Soundness
  imports Defs
begin

lemma context_invariance: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; \<forall>x \<tau>'. atom x \<in> fv_term e \<and> (x, \<tau>') \<in> \<Gamma> \<longrightarrow> (x, \<tau>') \<in> \<Gamma>' \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> e : \<tau>"
proof(nominal_induct \<Gamma> e \<tau> avoiding: \<Gamma>' rule: T.strong_induct)
  case (T_UnitI \<Gamma>)
  then show ?case using T.T_UnitI by simp
next
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case using T.T_VarI supp_at_base by fastforce
next
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then show ?case using T.T_AbsI by fastforce
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case by (metis T.T_AppI Un_iff term.fv_defs(3))
next
  case (T_LetI x \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then have 1: "atom x \<sharp> (\<Gamma>', e1)" by simp
  from T_LetI have 2: "(x, \<tau>1) # \<Gamma>' \<turnstile> e2 : \<tau>2" by simp
  show ?case using T.T_LetI[OF 1 2] using T_LetI by simp
qed

lemma free_in_context: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom x \<in> fv_term e \<rbrakk> \<Longrightarrow> \<exists>\<tau>'. (x, \<tau>') \<in> \<Gamma>"
proof(nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_UnitI \<Gamma>)
  then show ?case by simp
next
  case (T_VarI x' \<tau> \<Gamma>)
  then show ?case by (metis atom_eq_iff singletonD supp_at_base term.fv_defs(1))
next
  case (T_AbsI x' \<Gamma> \<tau>1 e \<tau>2)
  then show ?case by (metis Diff_iff Un_iff fresh_def insert_iff isin.simps(2) list.set(2) no_vars_in_ty term.fv_defs(2))
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case by auto
next
  case (T_LetI x' \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then show ?case by (metis Diff_iff UnE fresh_at_base(2) isin.simps(2) term.fv_defs(5))
qed

lemma fresh_term[simp]: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
  apply (nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
      apply (auto simp: fresh_Cons)
  using fresh_ineq_at_base fresh_not_isin apply force
  done

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_v_of_e e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (nominal_induct \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: T.strong_induct) auto

theorem progress: "[] \<turnstile> e : \<tau> \<Longrightarrow> is_v_of_e e \<or> (\<exists>e'. Step e e')"
proof (induction "[] :: \<Gamma>" e \<tau> rule: T.induct)
  case T_UnitI
  then show ?case by simp
next
  case (T_VarI x \<tau>)
  then show ?case by simp
next
  case (T_AbsI x \<tau>1 e \<tau>2)
  then show ?case by simp
next
  case (T_AppI e1 \<tau>1 \<tau>2 e2)
  note IH1 = T_AppI(2)
  note IH2 = T_AppI(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_v_of_e e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_v_of_e e2"
      from \<open>is_v_of_e e1\<close> T_AppI(1) have "\<exists>x e. e1 = (\<lambda>x:\<tau>1. e)" by (simp add: fun_ty_lam)
      then have "\<exists>e'. Step (App e1 e2) e'" using \<open>is_v_of_e e2\<close> ST_BetaI by blast
      then show ?thesis by simp
    next
      assume "\<exists>e2'. Step e2 e2'"
      then show ?thesis using ST_App2I \<open>is_v_of_e e1\<close> by blast
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
qed

lemma swap_term: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom y \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> ((x \<leftrightarrow> y) \<bullet> \<Gamma>) \<turnstile> (x \<leftrightarrow> y) \<bullet> e : \<tau>"
proof (nominal_induct \<Gamma> e \<tau> avoiding: x y rule: T.strong_induct)
  case (T_UnitI \<Gamma>)
  then show ?case by (simp add: T.T_UnitI)
next
  case (T_VarI z \<tau> \<Gamma>)
  then show ?case
    by (metis T.T_VarI T.eqvt flip_fresh_fresh no_vars_in_ty)
next
  case (T_AbsI x \<Gamma> \<tau>1 e \<tau>2)
  then show ?case
    by (metis T.T_AbsI T.eqvt flip_fresh_fresh no_vars_in_ty)
next
  case (T_AppI \<Gamma> e1 \<tau>1 \<tau>2 e2)
  then show ?case using T.T_AppI by fastforce
next
  case (T_LetI z \<Gamma> e1 \<tau>1 e2 \<tau>2)
  then have 1: "atom y \<sharp> (z, \<tau>1) # \<Gamma>" by (simp add: fresh_Cons fresh_at_base(2))

  from T_LetI have e1: "atom z \<sharp> (x \<leftrightarrow> y) \<bullet> e1" by (smt eq_eqvt flip_def fresh_at_base(2) fresh_eqvt swap_atom_simps(3))
  from T_LetI have "atom z \<sharp> (x \<leftrightarrow> y) \<bullet> \<Gamma>" by (metis flip_def fresh_at_base(2) fresh_permute_iff swap_atom_simps(3))
  then have 2: "atom z \<sharp> ((x \<leftrightarrow> y) \<bullet> \<Gamma>, (x \<leftrightarrow> y) \<bullet> e1)" using T_LetI e1 by simp

  from T_LetI have "(x \<leftrightarrow> y) \<bullet> ((z, \<tau>1) # \<Gamma>) = (z, \<tau>1)#((x \<leftrightarrow> y) \<bullet> \<Gamma>)" by (simp add: flip_fresh_fresh fresh_at_base(2))
  then have 3: "(z, \<tau>1) # (x \<leftrightarrow> y) \<bullet> \<Gamma> \<turnstile> (x \<leftrightarrow> y) \<bullet> e2 : \<tau>2" using T_LetI(6)[OF 1, of x] by simp

  show ?case using T.T_LetI[OF 2 3 T_LetI(8)[OF \<open>atom y \<sharp> \<Gamma>\<close>, of x]]
    by (smt "1" T_LetI.hyps(1) flip_fresh_fresh fresh_Cons fresh_PairD(1) fresh_at_base(2) term.perm_simps(5))
qed

lemma T_Abs_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<exists>\<tau>2. (x, \<tau>1)#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<tau>1 \<rightarrow> \<tau>2)"
proof (cases rule: T.cases[OF a])
  case (3 x' \<Gamma>' \<tau>1' e' \<tau>2)
  then show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis by (metis "3"(1) "3"(2) "3"(3) "3"(5) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(2))
  next
    case False
    then have 1: "atom x \<sharp> (x', \<tau>1') # \<Gamma>'" using b by (simp add: 3 fresh_Cons) 
    have 2: "((x' \<leftrightarrow> x) \<bullet> ((x', \<tau>1) # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using swap_term[OF "3"(5) 1, of x'] 3 by auto

    have 4: "(x' \<leftrightarrow> x) \<bullet> e' = e" by (metis "3"(2) Abs1_eq_iff(3) False flip_commute term.eq_iff(2))
    have 5: "((x' \<leftrightarrow> x) \<bullet> ((x', \<tau>1) # \<Gamma>)) = (x, \<tau>1)#\<Gamma>" by (smt "3"(1) "3"(4) Cons_eqvt Pair_eqvt b flip_at_simps(1) flip_fresh_fresh no_vars_in_ty)

    from 2 3 4 5 show ?thesis by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> \<turnstile> Let x e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<exists>\<tau>1. \<Gamma> \<turnstile> e1 : \<tau>1 \<and> (x, \<tau>1)#\<Gamma> \<turnstile> e2 : \<tau>"
proof (cases rule: T.cases[OF a])
  case (5 x' \<Gamma>' _ \<tau>1 e2' \<tau>2)
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis by (metis "5"(1) "5"(2) "5"(3) "5"(5) "5"(6) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(5))
  next
    case False
    then have 1: "atom x \<sharp> (x', \<tau>1) # \<Gamma>'" using b by (simp add: 5 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> ((x', \<tau>1)#\<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using swap_term[OF "5"(5) 1, of x'] 5 by blast

    have 3: "(x' \<leftrightarrow> x) \<bullet> e2' = e2" by (metis "5"(2) Abs1_eq_iff(3) False flip_commute term.eq_iff(5))
    have 4: "((x' \<leftrightarrow> x) \<bullet> ((x', \<tau>1) # \<Gamma>)) = (x, \<tau>1)#\<Gamma>" by (smt "5"(1) "5"(4) Cons_eqvt Pair_eqvt b flip_at_simps(1) flip_fresh_fresh fresh_PairD(1) no_vars_in_ty)

    from 2 3 4 5 show ?thesis by auto
  qed
qed simp_all

lemma substitution: "\<lbrakk> (x, \<tau>')#\<Gamma> \<turnstile> e : \<tau> ; [] \<turnstile> v : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> subst_term v x e : \<tau>"
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
      by (metis (no_types, lifting) Rep_name_inverse atom_name_def subst_term.simps(1) isin.simps(2) singletonD supp_at_base term.fv_defs(1))
  qed
next
  case (Lam y \<sigma> e)
  then obtain \<tau>2 where P: "(y, \<sigma>)#(x, \<tau>')#\<Gamma> \<turnstile> e : \<tau>2 \<and> \<tau> = (\<sigma> \<rightarrow> \<tau>2)" using T_Abs_Inv[OF Lam(7)] fresh_Cons fresh_Pair by blast
  then have "(x, \<tau>')#(y, \<sigma>)#\<Gamma> \<turnstile> e : \<tau>2" using context_invariance \<open>atom y \<sharp> x\<close> by auto
  then show ?case using Lam T_AbsI P by simp
next
  case (App e1 e2)
  obtain \<tau>1 where P: "((x, \<tau>') # \<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>) \<and> ((x, \<tau>') # \<Gamma> \<turnstile> e2 : \<tau>1)" using T.cases[OF App(3)] by fastforce
  then show ?case using T_AppI App by fastforce
next
  case Unit
  then show ?case using T.cases[OF Unit(1)] T_UnitI by auto
next
  case (Let y e1 e2)
  have "atom y \<sharp> e1" using Let.hyps(1) Let.hyps(4) Let.prems(1) T_Let_Inv fresh_Cons fresh_Pair fresh_term no_vars_in_ty by blast
  then have "atom y \<sharp> subst_term v x e1" by (simp add: Let.hyps(3) fresh_subst_term) 
  then have 0: "atom y \<sharp> (\<Gamma>, subst_term v x e1)" using Let fresh_Pair by simp

  obtain \<tau>1 where P: "(x, \<tau>')#\<Gamma> \<turnstile> e1 : \<tau>1 \<and> (y, \<tau>1)#(x, \<tau>')#\<Gamma> \<turnstile> e2 : \<tau>" using T_Let_Inv[OF Let(8)] Let fresh_Cons fresh_Pair by blast
  then have 1: "(x, \<tau>')#(y, \<tau>1)#\<Gamma> \<turnstile> e2 : \<tau>" using context_invariance Let(4) by force
  from P have 2: "(x, \<tau>')#\<Gamma> \<turnstile> e1 : \<tau>1" by simp

  have 3: "\<Gamma> \<turnstile> subst_term v x e1 : \<tau>1" using Let(6)[OF 2 Let(9)] .
  have 4: "(y, \<tau>1)#\<Gamma> \<turnstile> subst_term v x e2 : \<tau>" using Let(7)[OF 1 Let(9)] .

  show ?case using T_LetI[OF 0 4 3] using Let by simp
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
    then have "\<tau> = \<tau>1" using T_AppI.hyps(1) fun_ty_lam is_v_of_e.simps(2) term.eq_iff(2) by blast
    then have 1: "[] \<turnstile> e2 : \<tau>" using T_AppI(3) by simp

    have "[] \<turnstile> \<lambda> x : \<tau> . e : \<tau>1 \<rightarrow> \<tau>2" using T_AppI ST_BetaI by blast
    then have 2: "[(x, \<tau>)] \<turnstile> e : \<tau>2" using T_Abs_Inv fresh_Nil by fastforce

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
      then have "[(y, \<tau>1)] \<turnstile> e : \<tau>2" using swap_term[OF T_LetI(3) 1, of x] by (simp add: flip_fresh_fresh)
      then show ?thesis using T_LetI ST_SubstI substitution by auto
    qed
  next
    case (ST_LetI e2 x e)
    then show ?thesis by (metis (no_types, lifting) T.T_LetI T_LetI.hyps(1) T_LetI.hyps(3) T_LetI.hyps(5) fresh_Pair fresh_term term.eq_iff(5))
  qed
qed

definition beta_nf :: "term \<Rightarrow> bool" where
  "beta_nf e \<equiv> \<nexists>e'. Step e e'"

definition stuck :: "term \<Rightarrow> bool" where
  "stuck e \<equiv> \<not>is_v_of_e e \<and> beta_nf e"

inductive Steps :: "term \<Rightarrow> term \<Rightarrow> bool" (infix "\<longrightarrow>*" 70) where
  refl: "Steps e e"
| trans: "\<lbrakk> Steps e1 e2 ; Step e2 e3 \<rbrakk> \<Longrightarrow> Steps e1 e3"

lemma multi_preservation: "\<lbrakk> e \<longrightarrow>* e' ; [] \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> [] \<turnstile> e' : \<tau>"
  by (induction e e' rule: Steps.induct) (auto simp: preservation)

corollary soundness: "\<lbrakk> [] \<turnstile> e : \<tau> ; e \<longrightarrow>* e' \<rbrakk> \<Longrightarrow> \<not>(stuck e')"
  unfolding stuck_def beta_nf_def
  using progress multi_preservation by blast

lemma lam_equal: "Lam x \<tau> e = e2 \<Longrightarrow> \<exists>y e'. e2 = Lam y \<tau> e'"
  by (nominal_induct e2 avoiding: x rule: term.strong_induct) auto
lemma let_equal: "Let x e1 e2 = e \<Longrightarrow> \<exists>y e1' e2'. e = Let y e1' e2'"
  by (nominal_induct e2 avoiding: x rule: term.strong_induct) auto

lemma beta_nf_var[simp]: "beta_nf (Var x)" using beta_nf_def Step.cases by fastforce
lemma beta_nf_lam[simp]: "beta_nf (Lam x \<tau> e)" using beta_nf_def Step.cases by fastforce
lemma beta_nf_unit[simp]: "beta_nf Unit" using beta_nf_def Step.cases by fastforce
lemma beta_nf_value[simp]: "is_v_of_e e \<Longrightarrow> beta_nf e"
  by (nominal_induct e rule: term.strong_induct) auto

lemma beta_same[simp]: "\<lbrakk> e1 \<longrightarrow>* e1' ; beta_nf e1 \<rbrakk> \<Longrightarrow> e1 = e1'"
  by (induction e1 e1' rule: Steps.induct) (auto simp: beta_nf_def)

lemma subst_term_perm: "atom x' \<sharp> (x, e) \<Longrightarrow> subst_term v x e = subst_term v x' ((x \<leftrightarrow> x') \<bullet> e)"
  apply (nominal_induct e avoiding: x x' v rule: term.strong_induct)
      apply (auto simp: fresh_Pair fresh_at_base(2) flip_fresh_fresh)
  by (smt flip_at_base_simps(3) flip_commute flip_eqvt flip_fresh_fresh minus_flip permute_eqvt permute_eqvt subst_term.eqvt uminus_eqvt)

lemma step_deterministic: "\<lbrakk> Step e e1 ; Step e e2 \<rbrakk> \<Longrightarrow> e1 = e2"
proof (induction e e1 arbitrary: e2 rule: Step.induct)
  case (ST_BetaI v x \<tau> e)
  from \<open>App (\<lambda> x : \<tau> . e) v \<longrightarrow> e2\<close> show ?case
    apply cases
    apply (smt Abs1_eq_iff(3) flip_commute fresh_Pair fresh_at_base(2) subst_term_perm)
    using beta_nf_def beta_nf_lam apply blast
    using ST_BetaI.hyps beta_nf_def beta_nf_value by blast
next
  case (ST_SubstI v x e)
  from \<open>Let x v e \<longrightarrow> e2\<close> show ?case
    apply cases
      apply (smt Abs1_eq_iff(3) flip_commute fresh_Pair fresh_at_base(2) subst_term_perm)
  using ST_SubstI.hyps beta_nf_def beta_nf_value by blast
next
  case (ST_AppI e1' e2' e)
  from \<open>App e1' e \<longrightarrow> e2\<close> show ?case
    apply (cases)
    using ST_AppI beta_nf_def beta_nf_lam beta_nf_value by blast+
next
  case (ST_App2I v e1' e2')
  from \<open>App v e1' \<longrightarrow> e2\<close> show ?case
    apply (cases)
    using ST_App2I beta_nf_def beta_nf_lam beta_nf_value by blast+
next
  case (ST_LetI e1' e2' x e)
  from \<open>Let x e1' e \<longrightarrow> e2\<close> show ?case
    apply (cases)
    using ST_LetI.hyps beta_nf_def beta_nf_value apply blast
    using ST_LetI.IH term.eq_iff(5) by blast
qed

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
  then show ?case by (metis Steps.simps Steps_path beta_same path.elims(2) step_deterministic)
qed

end