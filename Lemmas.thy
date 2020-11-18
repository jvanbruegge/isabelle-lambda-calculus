theory Lemmas
  imports Syntax Defs
begin

(* atom x \<sharp> t' \<Longrightarrow> atom x \<sharp> subst t' x t *)
lemma fresh_after_subst_term: "atom x \<sharp> e' \<Longrightarrow> atom x \<sharp> subst_term e' x e"
  by (nominal_induct e avoiding: x e' rule: term.strong_induct) auto
lemma fresh_after_subst_type: "atom a \<sharp> \<tau> \<Longrightarrow> atom a \<sharp> subst_type \<tau> a \<sigma>"
  by (nominal_induct \<sigma> avoiding: a \<tau> rule: \<tau>.strong_induct) auto
lemma fresh_after_subst_term_type: "atom a \<sharp> \<tau> \<Longrightarrow> atom a \<sharp> subst_term_type \<tau> a e"
  by (nominal_induct e avoiding: a \<tau> rule: term.strong_induct) (auto simp: fresh_after_subst_type)

(* atom c \<sharp> t \<Longrightarrow> subst t' x t = subst t' c ((x \<leftrightarrow> c) \<bullet> t) *)
lemma subst_term_var_name: "atom c \<sharp> e \<Longrightarrow> subst_term e' x e = subst_term e' c ((x \<leftrightarrow> c) \<bullet> e)"
proof (nominal_induct e avoiding: c x e' rule: term.strong_induct)
  case (Let y \<tau> e1 e2)
  then show ?case by (smt flip_fresh_fresh fresh_Pair fresh_at_base(2) list.set(1) list.set(2) no_vars_in_ty singletonD subst_term.simps(7) term.fresh(7) term.perm_simps(7))
qed (auto simp: flip_fresh_fresh fresh_at_base)
lemma subst_type_var_name: "atom c \<sharp> \<sigma> \<Longrightarrow> subst_type \<tau> a \<sigma> = subst_type \<tau> c ((a \<leftrightarrow> c) \<bullet> \<sigma>)"
  by (nominal_induct \<sigma> avoiding: c a \<tau> rule: \<tau>.strong_induct) (auto simp: fresh_at_base)
lemma subst_term_type_var_name: "atom c \<sharp> e \<Longrightarrow> subst_term_type \<tau> a e = subst_term_type \<tau> c ((a \<leftrightarrow> c) \<bullet> e)"
proof (nominal_induct e avoiding: c a \<tau> rule: term.strong_induct)
  case (Lam x \<tau>1 e)
  then show ?case
    by (smt flip_fresh_fresh fresh_Pair fresh_at_base(2) list.set(1) list.set(2) singletonD subst_term_type.simps(3) subst_type_var_name term.fresh(5) term.perm_simps(5))
next
  case (Let x \<tau>1 e1 e2)
  then show ?case
    by (smt flip_def fresh_Pair fresh_at_base(2) list.set(1) list.set(2) singletonD subst_term_type.simps(7) subst_type_var_name swap_fresh_fresh term.fresh(7) term.perm_simps(7)) 
qed (auto simp: flip_fresh_fresh fresh_at_base subst_type_var_name)

(* [[atom a]]lst. t = [[atom a2]]lst. t2 \<Longrightarrow> subst t' a t = subst t' a2 t2 *)
lemma subst_term_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term t a e = subst_term t a' e'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_var_name)
lemma subst_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_type \<tau> a e = subst_type \<tau> a' e'"
  by (metis Abs1_eq_iff(3) flip_commute subst_type_var_name)
lemma subst_term_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term_type \<tau> a e = subst_term_type \<tau> a' e'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_type_var_name)

(* atom x \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (B x _) \<Gamma> *)
lemma fresh_not_isin_tyvar: "atom a \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (BTyVar a) \<Gamma>"
  apply (induction \<Gamma>) apply simp
  by (metis binder.fresh(2) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(4) isin.simps(5))
lemma fresh_not_isin_var: "atom x \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (BVar x \<tau>) \<Gamma>"
  apply (induction \<Gamma>) apply simp
  by (metis (mono_tags, lifting) binder.fresh(1) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(2) isin.simps(3))

end