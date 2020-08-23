theory Soundness
  imports Defs
begin

lemma context_invariance: "⟦ Γ ⊢ e : τ ; ∀x τ'. atom x ∈ fv_term e ∧ (x, τ') ∈ Γ ⟶ (x, τ') ∈ Γ' ⟧ ⟹ Γ' ⊢ e : τ"
proof(nominal_induct Γ e τ avoiding: Γ' rule: T.strong_induct)
  case (T_UnitI Γ)
  then show ?case using T.T_UnitI by simp
next
  case (T_VarI x τ Γ)
  then show ?case using T.T_VarI supp_at_base by fastforce
next
  case (T_AbsI x Γ τ1 e τ2)
  then show ?case using T.T_AbsI by fastforce
next
  case (T_AppI Γ e1 τ1 τ2 e2)
  then show ?case by (metis T.T_AppI Un_iff term.fv_defs(3))
next
  case (T_LetI x Γ e1 τ1 e2 τ2)
  then have 1: "atom x ♯ (Γ', e1)" by simp
  from T_LetI have 2: "(x, τ1) # Γ' ⊢ e2 : τ2" by simp
  show ?case using T.T_LetI[OF 1 2] using T_LetI by simp
qed

lemma free_in_context: "⟦ Γ ⊢ e : τ ; atom x ∈ fv_term e ⟧ ⟹ ∃τ'. (x, τ') ∈ Γ"
proof(nominal_induct Γ e τ avoiding: x rule: T.strong_induct)
  case (T_UnitI Γ)
  then show ?case by simp
next
  case (T_VarI x' τ Γ)
  then show ?case by (metis atom_eq_iff singletonD supp_at_base term.fv_defs(1))
next
  case (T_AbsI x' Γ τ1 e τ2)
  then show ?case by (metis Diff_iff Un_iff fresh_def insert_iff isin.simps(2) list.set(2) no_vars_in_ty term.fv_defs(2))
next
  case (T_AppI Γ e1 τ1 τ2 e2)
  then show ?case by auto
next
  case (T_LetI x' Γ e1 τ1 e2 τ2)
  then show ?case by (metis Diff_iff UnE fresh_at_base(2) isin.simps(2) term.fv_defs(5))
qed

lemma fresh_term[simp]: "⟦ Γ ⊢ e : τ ; atom x ♯ Γ ⟧ ⟹ atom x ♯ e"
  apply (nominal_induct Γ e τ avoiding: x rule: T.strong_induct)
      apply (auto simp: fresh_Cons)
  using fresh_ineq_at_base fresh_not_isin apply force
  done

lemma fun_ty_lam: "⟦ Γ ⊢ e : τ1 → τ2 ; is_v_of_e e ⟧ ⟹ ∃x e'. e = (λx:τ1. e')"
  by (nominal_induct Γ e "τ1 → τ2" rule: T.strong_induct) auto

theorem progress: "[] ⊢ e : τ ⟹ is_v_of_e e ∨ (∃e'. Step e e')"
proof (induction "[] :: Γ" e τ rule: T.induct)
  case T_UnitI
  then show ?case by simp
next
  case (T_VarI x τ)
  then show ?case by simp
next
  case (T_AbsI x τ1 e τ2)
  then show ?case by simp
next
  case (T_AppI e1 τ1 τ2 e2)
  note IH1 = T_AppI(2)
  note IH2 = T_AppI(4)

  from IH1 show ?case
  proof (elim disjE)
    assume "is_v_of_e e1"
    from IH2 show ?thesis
    proof (elim disjE)
      assume "is_v_of_e e2"
      from ‹is_v_of_e e1› T_AppI(1) have "∃x e. e1 = (λx:τ1. e)" by (simp add: fun_ty_lam)
      then have "∃e'. Step (App e1 e2) e'" using ‹is_v_of_e e2› ST_BetaI by blast
      then show ?thesis by simp
    next
      assume "∃e2'. Step e2 e2'"
      then show ?thesis using ST_App2I ‹is_v_of_e e1› by blast
    qed
  next
    assume "∃e1'. Step e1 e1'"
    then obtain e1' where "Step e1 e1'" by blast
    then have "Step (App e1 e2) (App e1' e2)" by (rule ST_AppI)
    then show ?thesis by blast
  qed
next
  case (T_LetI e1 τ1 x e2 τ2)
  then show ?case using ST_SubstI ST_LetI by blast
qed

lemma swap_term: "⟦ Γ ⊢ e : τ ; atom y ♯ Γ ⟧ ⟹ ((x ↔ y) ∙ Γ) ⊢ (x ↔ y) ∙ e : τ"
proof (nominal_induct Γ e τ avoiding: x y rule: T.strong_induct)
  case (T_UnitI Γ)
  then show ?case by (simp add: T.T_UnitI)
next
  case (T_VarI z τ Γ)
  then show ?case
    by (metis T.T_VarI T.eqvt flip_fresh_fresh no_vars_in_ty)
next
  case (T_AbsI x Γ τ1 e τ2)
  then show ?case
    by (metis T.T_AbsI T.eqvt flip_fresh_fresh no_vars_in_ty)
next
  case (T_AppI Γ e1 τ1 τ2 e2)
  then show ?case using T.T_AppI by fastforce
next
  case (T_LetI z Γ e1 τ1 e2 τ2)
  then have 1: "atom y ♯ (z, τ1) # Γ" by (simp add: fresh_Cons fresh_at_base(2))

  from T_LetI have e1: "atom z ♯ (x ↔ y) ∙ e1" by (smt eq_eqvt flip_def fresh_at_base(2) fresh_eqvt swap_atom_simps(3))
  from T_LetI have "atom z ♯ (x ↔ y) ∙ Γ" by (metis flip_def fresh_at_base(2) fresh_permute_iff swap_atom_simps(3))
  then have 2: "atom z ♯ ((x ↔ y) ∙ Γ, (x ↔ y) ∙ e1)" using T_LetI e1 by simp

  from T_LetI have "(x ↔ y) ∙ ((z, τ1) # Γ) = (z, τ1)#((x ↔ y) ∙ Γ)" by (simp add: flip_fresh_fresh fresh_at_base(2))
  then have 3: "(z, τ1) # (x ↔ y) ∙ Γ ⊢ (x ↔ y) ∙ e2 : τ2" using T_LetI(6)[OF 1, of x] by simp

  show ?case using T.T_LetI[OF 2 3 T_LetI(8)[OF ‹atom y ♯ Γ›, of x]]
    by (smt "1" T_LetI.hyps(1) flip_fresh_fresh fresh_Cons fresh_PairD(1) fresh_at_base(2) term.perm_simps(5))
qed

lemma T_Abs_Inv:
  assumes a: "Γ ⊢ (λx : τ1 . e) : τ" and b: "atom x ♯ Γ"
  shows "∃τ2. (x, τ1)#Γ ⊢ e : τ2 ∧ τ = (τ1 → τ2)"
proof (cases rule: T.cases[OF a])
  case (3 x' Γ' τ1' e' τ2)
  then show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis by (metis "3"(1) "3"(2) "3"(3) "3"(5) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(2))
  next
    case False
    then have 1: "atom x ♯ (x', τ1') # Γ'" using b by (simp add: 3 fresh_Cons) 
    have 2: "((x' ↔ x) ∙ ((x', τ1) # Γ)) ⊢ (x' ↔ x) ∙ e' : τ2" using swap_term[OF "3"(5) 1, of x'] 3 by auto

    have 4: "(x' ↔ x) ∙ e' = e" by (metis "3"(2) Abs1_eq_iff(3) False flip_commute term.eq_iff(2))
    have 5: "((x' ↔ x) ∙ ((x', τ1) # Γ)) = (x, τ1)#Γ" by (smt "3"(1) "3"(4) Cons_eqvt Pair_eqvt b flip_at_simps(1) flip_fresh_fresh no_vars_in_ty)

    from 2 3 4 5 show ?thesis by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "Γ ⊢ Let x e1 e2 : τ" and b: "atom x ♯ Γ"
  shows "∃τ1. Γ ⊢ e1 : τ1 ∧ (x, τ1)#Γ ⊢ e2 : τ"
proof (cases rule: T.cases[OF a])
  case (5 x' Γ' _ τ1 e2' τ2)
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis by (metis "5"(1) "5"(2) "5"(3) "5"(5) "5"(6) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(5))
  next
    case False
    then have 1: "atom x ♯ (x', τ1) # Γ'" using b by (simp add: 5 fresh_Cons)
    have 2: "((x' ↔ x) ∙ ((x', τ1)#Γ)) ⊢ (x' ↔ x) ∙ e2' : τ" using swap_term[OF "5"(5) 1, of x'] 5 by blast

    have 3: "(x' ↔ x) ∙ e2' = e2" by (metis "5"(2) Abs1_eq_iff(3) False flip_commute term.eq_iff(5))
    have 4: "((x' ↔ x) ∙ ((x', τ1) # Γ)) = (x, τ1)#Γ" by (smt "5"(1) "5"(4) Cons_eqvt Pair_eqvt b flip_at_simps(1) flip_fresh_fresh fresh_PairD(1) no_vars_in_ty)

    from 2 3 4 5 show ?thesis by auto
  qed
qed simp_all

definition closed :: "term ⇒ bool" where
  "closed x ≡ fv_term x = {}"

lemma typeable_closed: "[] ⊢ e : τ ⟹ closed e"
  sorry

lemma substitution: "⟦ (x, τ')#Γ ⊢ e : τ ; [] ⊢ v : τ' ⟧ ⟹ Γ ⊢ esubst_e v x e : τ"
proof (nominal_induct e avoiding: Γ τ v x τ' rule: term.strong_induct)
  case (Var y)
  then show ?case
  proof (cases "x = y")
    case True
    then have "τ = τ'" using Var T.cases by fastforce
    then show ?thesis using True Var context_invariance by fastforce
  next
    case False
    then show ?thesis using Var context_invariance
      by (metis (no_types, lifting) Rep_name_inverse atom_name_def esubst_e.simps(1) isin.simps(2) singletonD supp_at_base term.fv_defs(1))
  qed
next
  case (Lam y σ e)
  then obtain τ2 where P: "(y, σ)#(x, τ')#Γ ⊢ e : τ2 ∧ τ = (σ → τ2)" using T_Abs_Inv[OF Lam(7)] fresh_Cons fresh_PairE by blast
  then have "(x, τ')#(y, σ)#Γ ⊢ e : τ2" using context_invariance ‹atom y ♯ x› by auto
  then show ?case using Lam T_AbsI P by simp
next
  case (App e1 e2)
  obtain τ1 where P: "((x, τ') # Γ ⊢ e1 : τ1 → τ) ∧ ((x, τ') # Γ ⊢ e2 : τ1)" using T.cases[OF App(3)] by fastforce
  then show ?case using T_AppI App by fastforce
next
  case Unit
  then show ?case using T.cases[OF Unit(1)] T_UnitI by auto
next
  case (Let y e1 e2)
  have "atom y ♯ e1" using Let.hyps(1) Let.hyps(4) Let.prems(1) T_Let_Inv fresh_Cons fresh_Pair fresh_term no_vars_in_ty by blast
  then have "atom y ♯ esubst_e v x e1" by (simp add: Let.hyps(3) fresh_esubst_e) 
  then have 0: "atom y ♯ (Γ, esubst_e v x e1)" using Let fresh_Pair by simp

  obtain τ1 where P: "(x, τ')#Γ ⊢ e1 : τ1 ∧ (y, τ1)#(x, τ')#Γ ⊢ e2 : τ" using T_Let_Inv[OF Let(8)] Let fresh_Cons fresh_Pair by blast
  then have 1: "(x, τ')#(y, τ1)#Γ ⊢ e2 : τ" using context_invariance Let(4) by force
  from P have 2: "(x, τ')#Γ ⊢ e1 : τ1" by simp

  have 3: "Γ ⊢ esubst_e v x e1 : τ1" using Let(6)[OF 2 Let(9)] .
  have 4: "(y, τ1)#Γ ⊢ esubst_e v x e2 : τ" using Let(7)[OF 1 Let(9)] .

  show ?case using T_LetI[OF 0 4 3] using Let by simp
qed

(*theorem preservation: "⟦ [] ⊢ e : τ ; Step e e' ⟧ ⟹ [] ⊢ e' : τ"
proof (induction "[] :: Γ" e τ arbitrary: e' rule: T.induct)
case T_UnitI
  then show ?case using Step.cases by blast
next
  case (T_VarI x τ)
  then show ?case using Step.cases by blast
next
  case (T_AbsI x τ1 e τ2)
  then show ?case using Step.cases by blast
next
  case (T_AppI e1 τ1 τ2 e2)
  from ‹App e1 e2 ⟶ e'› show ?case
  proof cases
    case (ST_BetaI x τ e)
    then show ?thesis using substitution T.cases T_AppI by blast
  next
    case (ST_AppI e2)
    then show ?thesis using T_AppI T.T_AppI by blast
  next
    case (ST_App2I e2)
    then show ?thesis using T_AppI T.T_AppI by blast
  qed
next
  case (T_LetI e1 τ1 x e2 τ2)
  from ‹Let x e1 e2 ⟶ e'› show ?case
  proof (cases)
    case ST_SubstI
    then show ?thesis using substitution T.cases T_LetI by blast
  next
    case (ST_LetI e2)
    then show ?thesis using T_LetI T.T_LetI by blast
  qed
qed

definition stuck :: "e ⇒ bool" where
  "stuck e ≡ ¬(is_v_of_e e ∨ (∃e'. Step e e'))"

inductive Steps :: "e ⇒ e ⇒ bool" (infix "⟶*" 70) where
  refl: "Steps e e"
| trans: "⟦ Steps e1 e2 ; Step e2 e3 ⟧ ⟹ Steps e1 e3"

lemma multi_preservation: "⟦ e ⟶* e' ; [] ⊢ e : τ ⟧ ⟹ [] ⊢ e' : τ"
  apply (induction e e' rule: Steps.induct)
  using preservation by blast+

corollary soundness: "⟦ [] ⊢ e : τ ; e ⟶* e' ⟧ ⟹ ¬(stuck e')"
  unfolding stuck_def
  using progress multi_preservation by blast
*)
end