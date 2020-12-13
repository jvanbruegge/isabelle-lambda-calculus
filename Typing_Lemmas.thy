theory Typing_Lemmas
  imports Typing Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

lemma fun_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> \<exists>x e'. e = (\<lambda>x:\<tau>1. e')"
  by (induction \<Gamma> e "\<tau>1 \<rightarrow> \<tau>2" rule: Tm_induct) auto

lemma forall_ty_lam: "\<lbrakk> \<Gamma> \<turnstile> e : (\<forall> a:k. \<sigma>) ; is_value e \<rbrakk> \<Longrightarrow> \<exists>a' e'. e = (\<Lambda> a':k. e')"
  by (induction \<Gamma> e "(\<forall> a:k. \<sigma>)" rule: Tm_induct) auto

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

lemma Ty_Forall_Inv:
  assumes a: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a:k. \<sigma>) : \<tau>" and b: "atom a \<sharp> \<Gamma>"
  shows "BTyVar a k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<and> \<tau> = \<star>"
proof (cases rule: Ty.cases[OF a])
  case (5 a' k' \<Gamma>' \<sigma>')
  then have 1: "BTyVar a' k # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" by simp
  have "(a' \<leftrightarrow> a) \<bullet> \<sigma>' = \<sigma>" using Abs_rename_body[of a' \<sigma>' a \<sigma>] 5(2) by auto
  then have 2: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using Ty.eqvt[OF 1, of "(a' \<leftrightarrow> a)"] by auto
  have 3: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # ((a' \<leftrightarrow> a) \<bullet> \<Gamma>)" using Cons_eqvt flip_fresh_fresh by force
  have 4: "(a' \<leftrightarrow> a) \<bullet> \<Gamma> = \<Gamma>" using b flip_fresh_fresh "5"(1) "5"(4) context_cons_fresh_tyvar ty_context_valid by blast
  show ?thesis using 2 3 4 5(3) by argo
qed simp_all

lemma isin_subset:
  fixes \<Gamma>::"\<Gamma>"
  assumes "\<turnstile> \<Gamma>' @ \<Gamma>"
  shows "bndr \<in> \<Gamma> \<longrightarrow> bndr \<in> (\<Gamma>' @ \<Gamma>)"
proof
  assume "bndr \<in> \<Gamma>"
  then show "bndr \<in> (\<Gamma>' @ \<Gamma>)"
  using assms proof (induction \<Gamma>' arbitrary: \<Gamma>)
    case (Cons b \<Gamma>2)
    have 1: "\<turnstile> \<Gamma>2 @ \<Gamma>" using Cons(3) Ctx.cases by auto
    have 2: "bndr \<in> (\<Gamma>2 @ \<Gamma>)" by (rule Cons(1)[OF Cons(2) 1])
    show ?case
    proof (cases b rule: binder.exhaust)
      case (BVar x \<tau>)
      then have "atom x \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons context_cons_fresh_var by auto
      then show ?thesis using 2 BVar fresh_not_isin_var by (cases bndr rule: binder.exhaust) auto
    next
      case (BTyVar a k)
      then have "atom a \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons context_cons_fresh_tyvar by auto
      then show ?thesis using 2 BTyVar fresh_not_isin_tyvar by (cases bndr rule: binder.exhaust) auto
    qed
  qed auto
qed

lemma isin_kind_same: "\<lbrakk> BTyVar a k1 \<in> (\<Gamma>' @ BTyVar a k2 # \<Gamma>) ; \<turnstile> \<Gamma>' @ BTyVar a k2 # \<Gamma> \<rbrakk> \<Longrightarrow> k1 = k2"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case by (cases rule: Ctx.cases[OF Cons(3)]) (auto split: if_splits simp: fresh_Cons fresh_append fresh_at_base(2))
qed auto

lemma isin_subst: "\<lbrakk> BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>) ; \<turnstile> \<Gamma>' @ BTyVar b k2 # \<Gamma> ; a \<noteq> b \<rbrakk> \<Longrightarrow> BTyVar a k \<in> (\<Gamma>'[\<sigma>/b] @ \<Gamma>)"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case
  proof (cases rule: Ctx.cases[OF Cons(3)])
    case (2 \<Gamma>2 c k3)
    then have "BTyVar a k = bndr \<or> BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>)" by (metis Cons.prems(1) Cons_eq_append_conv isin.simps(5) list.inject) 
    then show ?thesis
    proof
      assume a: "BTyVar a k = bndr"
      then show ?thesis using 2 Cons by auto
    next
      assume "BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>)"
      then show ?thesis using 2 Cons fresh_not_isin_tyvar by auto
    qed
  next
    case (3 \<Gamma> \<tau> x)
    then show ?thesis using Cons by auto
  qed simp
qed simp

lemma context_split_valid: "\<turnstile> \<Gamma>' @ \<Gamma> \<Longrightarrow> \<turnstile> \<Gamma>"
proof (induction \<Gamma>')
  case (Cons b \<Gamma>)
  then show ?case by (cases b rule: binder.exhaust) auto
qed (auto simp: Ctx_Empty)

end
