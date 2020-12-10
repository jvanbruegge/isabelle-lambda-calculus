theory Typing_Lemmas
  imports Typing Lemmas
begin

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (nominal_induct \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: T.strong_induct) auto

lemma ty_fresh_vars: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (nominal_induct \<Gamma> \<tau> k avoiding: a rule: Ty.strong_induct)
  case (Ty_Var a \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_tyvar by force
qed (auto simp: fresh_Cons)

(* inversion rules for abstractions *)
lemma T_Abs_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  obtains \<tau>2 where "BVar x \<tau>1#\<Gamma> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)" "\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 : \<star>"
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
  shows "\<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>"
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
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using 5(1) 5(3) T.eqvt[OF 5(5)] no_vars_in_ty flip_fresh_fresh by metis
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "5"(1) "5"(4) Cons_eqvt b binder.perm_simps(1) flip_at_simps(1) flip_fresh_fresh fresh_PairD(1) no_vars_in_ty)
    from 2 3 5 swap show ?thesis by auto
  qed
qed simp_all

lemma T_AbsT_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<Lambda> a : k . e) : \<tau>" and b: "atom a \<sharp> \<Gamma>" "atom a \<sharp> \<tau>"
  obtains \<sigma> where "BTyVar a k # \<Gamma> \<turnstile> e : \<sigma>" "\<tau> = TyForall a k \<sigma>"
proof (cases rule: T.cases[OF a])
  case (7 a' k' \<Gamma>' e' \<sigma>')
  have swap: "(a \<leftrightarrow> a') \<bullet> e' = e" by (metis (no_types, lifting) "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(6))
  then have x: "BTyVar a k # \<Gamma> \<turnstile> e : (a \<leftrightarrow> a') \<bullet> \<sigma>'"
    by (smt "7"(1) "7"(2) "7"(4) "7"(5) Cons_eqvt T.eqvt b(1) binder.perm_simps(2) flip_at_simps(2) flip_def no_tyvars_in_kinds swap_fresh_fresh term.eq_iff(6))
  have "\<tau> = (\<forall>a : k . (a \<leftrightarrow> a') \<bullet> \<sigma>')"
    by (metis "7"(2) "7"(3) Abs1_eq_iff(3) Nominal2_Base.swap_self \<tau>.eq_iff(5) \<tau>.fresh(5) b(2) empty_iff flip_def insert_iff list.set(1) list.set(2) no_vars_in_ty swap_fresh_fresh term.eq_iff(6))
  then show ?thesis using x that by blast
qed simp_all

(* freshness *)
lemma fresh_term_var: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (x::var) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom x \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: x rule: T.strong_induct)
  case (T_VarI x \<tau> \<Gamma>)
  then show ?case using fresh_ineq_at_base fresh_not_isin_var by force
qed (auto simp: fresh_Cons)

end
