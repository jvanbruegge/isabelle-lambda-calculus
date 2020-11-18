theory Typing_Lemmas
  imports Typing Lemmas
begin

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (nominal_induct \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: T.strong_induct) auto

lemma ty_fresh_vars: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (nominal_induct \<Gamma> \<tau> avoiding: a rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_tyvar by force
next
  case (Ty_Forall a \<Gamma> \<sigma>)
  then show ?case by (metis \<tau>.fresh(4) binder.supp(2) fresh_Cons fresh_def list.set(1) list.simps(15) supp_at_base)
qed auto

(* inversion rules for abstractions *)
lemma T_Abs_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  obtains \<tau>2 where "BVar x \<tau>1#\<Gamma> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1"
proof (cases rule: T.cases[OF a])
  case (3 x' \<Gamma>' \<tau>1' e' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" by (metis "3"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(5))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 3 swap that by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 3 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using T.eqvt
      by (metis "3"(1) "3"(2) "3"(6) flip_def no_vars_in_ty swap_fresh_fresh term.eq_iff(5))

    have "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "3"(1) "3"(4) Cons_eqvt b binder.perm_simps(1) flip_at_simps(1) flip_def no_vars_in_ty swap_fresh_fresh)

    then show ?thesis using 1 2 3 swap that by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
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
  obtains \<sigma> where "BTyVar a # \<Gamma> \<turnstile> e : \<sigma>" "\<tau> = TyForall a \<sigma>"
proof (cases rule: T.cases[OF a])
  case (7 a' \<Gamma>' e' \<sigma>')
  have swap: "(a \<leftrightarrow> a') \<bullet> e' = e" by (metis (no_types, lifting) "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(6))
  then have x: "BTyVar a # \<Gamma> \<turnstile> e : (a \<leftrightarrow> a') \<bullet> \<sigma>'" by (smt "7"(1) "7"(4) "7"(5) Cons_eqvt T.eqvt b binder.perm_simps(2) flip_at_simps(2) flip_def fresh_PairD(2) swap_fresh_fresh)
  have "\<tau> = (\<forall>a . (a \<leftrightarrow> a') \<bullet> \<sigma>')"
    by (metis "7"(3) "7"(5) Ty_Forall Ty_Var \<tau>.fresh(2) \<tau>.fresh(4) \<tau>.perm_simps(4) b(2) binder.fresh(2) flip_at_simps(2) flip_fresh_fresh fresh_Cons fresh_not_isin_tyvar isin.simps(5) ty_fresh_vars)
  then show ?thesis using x that by blast
qed simp_all

(* freshness *)
lemma fresh_term_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_var by force
qed (auto simp: fresh_Cons)

end
