theory Typing_Lemmas
  imports Typing Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (induction \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: Tm_induct) auto

lemma ty_fresh_vars: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> : k ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> \<tau>"
proof (nominal_induct \<Gamma> \<tau> k avoiding: a rule: Ty_strong_induct)
  case (Var \<Gamma> a k)
  then show ?case using fresh_at_base(2) fresh_not_isin_tyvar by fastforce
qed (auto simp: fresh_Cons)

lemma term_fresh_tyvars: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; atom (a::tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> e"
proof (nominal_induct \<Gamma> e \<tau> avoiding: a rule: Tm_strong_induct)
  case (Abs \<Gamma> x \<tau>1 e \<tau>2)
  then have "atom a \<sharp> \<tau>1" by (metis Ctx.cases binder.distinct(1) binder.eq_iff(1) list.inject list.simps(3) tm_context_valid ty_fresh_vars)
  then show ?case by (simp add: Abs fresh_Cons)
next
  case (Let \<Gamma> e1 e2 \<tau>1 \<tau>2 x)
  then have "atom a \<sharp> \<tau>1" by (metis Ctx.cases binder.distinct(1) binder.eq_iff(1) list.inject list.simps(3) tm_context_valid ty_fresh_vars)
  then show ?case by (simp add: Let fresh_Cons)
qed (auto simp: fresh_Cons ty_fresh_vars)

(* inversion rules for abstractions *)
lemma T_Abs_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  obtains \<tau>2 where "BVar x \<tau>1#\<Gamma> \<turnstile> e : \<tau>2" "\<tau> = (\<tau>1 \<rightarrow> \<tau>2)"
proof (cases rule: Tm.cases[OF a])
  case (2 x' \<tau>1' \<Gamma>' e' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" by (metis "2"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(5))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 2 swap that by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 2 fresh_Cons)
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" by (metis "2"(1) "2"(2) "2"(4) Tm.eqvt flip_fresh_fresh no_vars_in_ty term.eq_iff(5))
    have "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "2"(1) "2"(4) Cons_eqvt b binder.perm_simps(1) context_cons_fresh_var flip_at_simps(2) flip_commute flip_fresh_fresh no_vars_in_ty tm_context_valid)
    then show ?thesis using 1 2 3 swap that by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<Gamma> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>"
proof (cases rule: Tm.cases[OF a])
  case (7 \<Gamma>' e1' \<tau>1' x' e2' \<tau>2)
  have swap: "(x' \<leftrightarrow> x) \<bullet> e2' = e2" by (metis "7"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_flip_cancel permute_plus term.eq_iff(7))
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 7 swap by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1 # \<Gamma>'" using b by (simp add: 7 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" by (metis "7"(1) "7"(2) "7"(3) "7"(5) Tm.eqvt flip_fresh_fresh no_vars_in_ty term.eq_iff(7))
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "1" "7"(1) "7"(5) Cons_eqvt binder.perm_simps(1) context_cons_fresh_var flip_at_simps(1) flip_fresh_fresh fresh_Cons no_vars_in_ty tm_context_valid)
    from 2 3 7 swap show ?thesis by auto
  qed
qed simp_all

lemma T_AbsT_Inv:
  assumes a: "\<Gamma> \<turnstile> (\<Lambda> a : k . e) : \<tau>" and b: "atom a \<sharp> \<Gamma>" "atom a \<sharp> \<tau>"
  obtains \<sigma> where "BTyVar a k # \<Gamma> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a:k. \<sigma>)"
proof (cases rule: Tm.cases[OF a])
  case (4 a' k' \<Gamma>' e' \<sigma>')
  then have fresh: "atom a' \<sharp> \<Gamma>" using context_valid context_cons_fresh_tyvar by blast
  have swap: "(a \<leftrightarrow> a') \<bullet> e' = e" by (metis (no_types, lifting) "4"(2) Abs1_eq_iff(3) Nominal2_Base.swap_self add_flip_cancel flip_def permute_eq_iff permute_plus term.eq_iff(6))
  show ?thesis
  proof (cases "atom a = atom a'")
    case True
    then show ?thesis by (metis "4"(1) "4"(2) "4"(3) "4"(4) Abs1_eq_iff(3) atom_eq_iff term.eq_iff(6) that)
  next
    case False
    then have 1: "atom a \<sharp> BTyVar a' k # \<Gamma>" using b by (simp add: 4 fresh_Cons)
    have 2: "((a \<leftrightarrow> a') \<bullet> (BTyVar a' k # \<Gamma>)) \<turnstile> (a \<leftrightarrow> a') \<bullet> e' : (a \<leftrightarrow> a') \<bullet> \<sigma>'" using Tm.eqvt[OF 4(4)] by (metis "4"(1) "4"(2) term.eq_iff(6))
    have "((a \<leftrightarrow> a') \<bullet> (BTyVar a' k # \<Gamma>)) = ((a \<leftrightarrow> a') \<bullet> BTyVar a' k) # \<Gamma>" using 1 fresh flip_fresh_fresh b(1) by simp
    then have 3: "((a \<leftrightarrow> a') \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # \<Gamma>" by (simp add: flip_fresh_fresh)
    then show ?thesis
      by (metis "1" "2" "4"(2) "4"(3) Abs1_eq_iff(3) False \<tau>.eq_iff(5) \<tau>.fresh(5) b(2) binder.fresh(2) fresh_Cons fresh_def list.set(1) list.set(2) supp_at_base term.eq_iff(6) that)
  qed
qed simp_all

end
