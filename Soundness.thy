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

(*lemma free_in_context: "⟦ atom (x::name) ∈ fv_term e ; Γ ⊢ e : τ ⟧ ⟹ ∃τ'. (x, τ') ∈ Γ"
proof(nominal_induct e avoiding: x Γ τ rule: term.strong_induct)
  case (Var y)
  then have "fv_term (Var y) = { atom y }" unfolding supp_def by (simp add: supp_at_base)
  then have "atom x = atom y" using ‹atom x ∈ fv_term (Var y)› by simp
  then have "(x, τ) ∈ Γ" using T.cases[OF ‹Γ ⊢ Var y : τ›] by fastforce
  then show ?case by blast
next
  case (Lam y τ1 e)
  then have 1: "atom x ∈ fv_term e" using fresh_def by fastforce

  from Lam obtain y' e' τ2 where 2: "(y', τ1)#Γ ⊢ e' : τ2 ∧ atom y' ♯ Γ ∧ (λy : τ1 . e) = (λy' : τ1 . e')" using T_Abs_Inv by blast

  then show ?case sorry
next
  case (App e1 e2)
  obtain τ1 where "Γ ⊢ e1 : τ1 → τ ∧ Γ ⊢ e2 : τ1" using T.cases[OF ‹Γ ⊢ App e1 e2 : τ›] by fastforce
  then show ?case using App by auto
next
  case Unit
  then show ?case by simp
next
  case (Let y e1 e2)
  obtain τ' where P: "Γ ⊢ e1 : τ'" using T.cases[OF ‹Γ ⊢ Let y e1 e2 : τ›] by fastforce
  from Let have "atom x ∈ fv_term e1 ∨ atom x ∈ fv_term e2" by auto
  then show ?case
  proof
    assume x: "atom x ∈ fv_term e1"
    obtain τ' where P: "Γ ⊢ e1 : τ'" using T.cases[OF ‹Γ ⊢ Let y e1 e2 : τ›] by fastforce
    show ?thesis using Let(4)[OF x P] by simp
  next
    assume x: "atom x ∈ fv_term e2"
    from Let have 1: "atom x ≠ atom y" by simp
    have P: "(y, τ')#Γ ⊢ e2 : τ" using T.cases[OF ‹Γ ⊢ Let y e1 e2 : τ›] sorry
    show ?thesis using Let(5)[OF x P] 1 by simp
  qed
qed

lemma fun_ty_lam: "⟦ is_v_of_e e ; Γ ⊢ e : τ1 → τ2 ⟧ ⟹ ∃x e'. e = (λx:τ1. e')"
  apply (cases e)
  sorry

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

definition closed :: "e ⇒ bool" where
  "closed x ≡ fve_e x = []"


corollary typeable_closed: "[] ⊢ e : τ ⟹ closed e"
  unfolding closed_def
  using free_in_context last_in_set by fastforce

lemma context_invariance: "⟦ Γ ⊢ e : τ ; ∀x τ'. x ∈ set (fve_e e) ∧ (x, τ') ∈ Γ ⟶ (x, τ')∈Γ' ⟧ ⟹ Γ' ⊢ e : τ"
proof (induction Γ e τ arbitrary: Γ' rule: T.induct)
  case (T_UnitI Γ)
  then show ?case by (simp add: T.T_UnitI)
next
  case (T_VarI x τ Γ)
  then show ?case by (auto simp: T.T_VarI)
next
  case (T_AbsI y τ1 Γ e τ2)
  then show ?case by (simp add: T.T_AbsI list_minus_set)
next
  case (T_AppI Γ e1 τ1 τ2 e2)
  then show ?case by auto (metis (mono_tags, lifting) T.T_AppI)
next
  case (T_LetI e1 τ1 x e2 τ2)
  then show ?case apply auto
    by (smt DiffI T.T_LetI empty_iff insertE isin.simps(2) list.set(1) list.set(2) list_minus_set) 
qed

lemma substitution: "⟦ (x, τ')#Γ ⊢ e : τ ; [] ⊢ v : τ' ⟧ ⟹ Γ ⊢ esubst_e v x e : τ"
proof (induction e arbitrary: Γ τ v x τ')
  case (Var y)
  then show ?case
  proof (cases "x = y")
    case True
    then have "τ = τ'" using Var T.cases by fastforce
    then show ?thesis using True Var context_invariance by fastforce
  next
    case False
    then show ?thesis using Var context_invariance by simp
  qed
next
  case (Lam y σ e)
  let ?lam = "λ y : σ . e"
  from Lam show ?case
  proof (cases "x = y")
    case True
    then have "esubst_e v x ?lam = ?lam" by simp
    then show ?thesis
      by (smt Diff_iff Lam.prems(1) True context_invariance fve_e.simps(2) insert_iff isin.simps(2) list.simps(15) list_minus_set)
  next
    case False
    then obtain τ2 where P: "τ = (σ → τ2)" using Lam(2) T.cases by blast
    then have "(y, σ)#(x, τ')#Γ ⊢ e : τ2" using T.cases Lam by blast
    then have "(x, τ')#(y, σ)#Γ ⊢ e : τ2" using context_invariance False by force
    then show ?thesis using False Lam T_AbsI P by simp
  qed
next
  case (App e1 e2)
  from ‹(x, τ') # Γ ⊢ App e1 e2 : τ› obtain τ1 where P: "((x, τ') # Γ ⊢ e1 : τ1 → τ) ∧ ((x, τ') # Γ ⊢ e2 : τ1)" using T.cases by blast
  then show ?case using T_AppI App by fastforce
next
  case Unit
  then show ?case apply auto using T_UnitI T.cases by blast
next
  case (Let y e1 e2)
  from Let(3) obtain τ1 where P: "(x, τ')#Γ ⊢ e1 : τ1 ∧ (y, τ1)#(x, τ')#Γ ⊢ e2 : τ" using T.cases by blast
  from Let show ?case
  proof (cases "x = y")
    case True
    then have x: "esubst_e v x (Let y e1 e2) = Let y (esubst_e v x e1) e2" by simp
    then have e1: "Γ ⊢ esubst_e v x e1 : τ1" using Let P by blast
    from True Let have e2: "(y, τ1) # Γ ⊢ e2 : τ" by (smt P context_invariance isin.simps(2))
    then show ?thesis using T_LetI[OF e1 e2] x by simp
  next
    case False
    then have "(x, τ')#(y, τ1)#Γ ⊢ e2 : τ" using P context_invariance by fastforce
    then show ?thesis
      by (smt False Let.IH(1) Let.IH(2) Let.prems(2) P T_LetI empty_iff esubst_e.simps(5) list.set(1) set_ConsD)
  qed
qed

theorem preservation: "⟦ [] ⊢ e : τ ; Step e e' ⟧ ⟹ [] ⊢ e' : τ"
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