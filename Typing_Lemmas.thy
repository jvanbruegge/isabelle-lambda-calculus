theory Typing_Lemmas
  imports Typing Lemmas
begin

no_notation Set.member  ("(_/ : _)" [51, 51] 50)

lemma fun_ty_lam: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : \<tau>1 \<rightarrow> \<tau>2 ; is_value e \<rbrakk> \<Longrightarrow> (\<exists>x e'. e = (\<lambda>x:\<tau>1. e')) \<or> (\<exists>D tys vals. e = Ctor D tys vals)"
  by (induction \<Gamma> \<Delta> e "\<tau>1 \<rightarrow> \<tau>2" rule: Tm.induct) auto
lemma forall_ty_lam: "\<lbrakk> \<Gamma> , \<Delta> \<turnstile> e : (\<forall> a:k. \<sigma>) ; is_value e \<rbrakk> \<Longrightarrow> (\<exists>a' e'. e = (\<Lambda> a':k. e')) \<or> (\<exists>D tys vals. e = Ctor D tys vals)"
  by (induction \<Gamma> \<Delta> e "(\<forall> a:k. \<sigma>)" rule: Tm.induct) auto

lemma context_cons_valid[elim]: "(\<Delta>::\<Delta>) \<turnstile> bndr # \<Gamma> \<Longrightarrow> (\<Delta> \<turnstile> \<Gamma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases rule: Ctx.cases) (auto simp: context_valid(1))

(* inversion rules for abstractions *)
lemma T_Abs_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> (\<lambda>x : \<tau>1 . e) : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  obtains \<tau>2 where "BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e : \<tau>2" "\<tau> = arrow_app \<tau>1 \<tau>2"
proof (cases rule: Tm.cases[OF a])
  case (2 x' \<tau>1' \<Gamma>' \<Delta>' e' \<tau>2)
  then have swap: "(x' \<leftrightarrow> x) \<bullet> e' = e" using Abs_rename_body[of x' e' x e] by auto
  have valid: "\<turnstile> \<Delta>" using axioms_valid(3)[OF 2(5)] 2(2) by simp
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 2 swap that by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1' # \<Gamma>'" using b by (simp add: 2 fresh_Cons)
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1 # \<Gamma>)) , \<Delta> \<turnstile> (x' \<leftrightarrow> x) \<bullet> e' : \<tau>2" using 2 Tm.eqvt[OF 2(5), of "(x' \<leftrightarrow> x)"] by fastforce
    have "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>)) = BVar x \<tau>1 # \<Gamma>"
      by (metis "1" "2"(1) "2"(5) CtxE(2) binder.perm_simps(1) context_valid_tm flip_at_simps(1) flip_fresh_fresh fresh_Cons perm_\<tau>_vars)
    then show ?thesis using 1 2 3 swap that by auto
  qed
qed simp_all

lemma T_Let_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>" and b: "atom x \<sharp> \<Gamma>"
  shows "\<Gamma> , \<Delta> \<turnstile> e1 : \<tau>1 \<and> BVar x \<tau>1 # \<Gamma> , \<Delta> \<turnstile> e2 : \<tau>"
proof (cases rule: Tm.cases[OF a])
  case (9 \<Gamma>' \<Delta>' e1' \<tau>1' x' e2' \<tau>2')
  have swap: "(x' \<leftrightarrow> x) \<bullet> e2' = e2" using Abs_rename_body[of x' e2' x e2] 9(3) by simp
  show ?thesis
  proof (cases "atom x' = atom x")
    case True
    then show ?thesis using 9 swap by auto
  next
    case False
    then have 1: "atom x \<sharp> BVar x' \<tau>1 # \<Gamma>'" using b by (simp add: 9 fresh_Cons)
    have 2: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1#\<Gamma>)) , \<Delta> \<turnstile> (x' \<leftrightarrow> x) \<bullet> e2' : \<tau>" using Tm.eqvt[OF 9(6), of "(x' \<leftrightarrow> x)"] 9 by auto
    have 3: "((x' \<leftrightarrow> x) \<bullet> (BVar x' \<tau>1) # ((x' \<leftrightarrow> x) \<bullet> \<Gamma>)) = BVar x \<tau>1#\<Gamma>"
      by (metis "1" 9(1,6) CtxE(2) binder.perm_simps(1) context_valid_tm flip_at_simps(1) flip_def fresh_Cons perm_\<tau>_vars swap_fresh_fresh)
    from 2 3 9 swap show ?thesis by auto
  qed
qed simp_all

lemma T_AbsT_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile> (\<Lambda> a : k . e) : \<tau>" and b: "atom a \<sharp> \<Gamma>" "atom a \<sharp> \<tau>"
  obtains \<sigma> where "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : \<sigma>" "\<tau> = (\<forall> a:k. \<sigma>)"
proof (cases rule: Tm.cases[OF a])
  case (4 a' k' \<Gamma>' \<Delta>' e' \<sigma>')
  then have fresh: "atom a' \<sharp> \<Gamma>" by (cases rule: Ctx.cases[OF context_valid(2)[OF 4(5)]]) auto
  have swap: "(a' \<leftrightarrow> a) \<bullet> e' = e" using Abs_rename_body[of a' e' a e] 4(3) by simp
  have valid: "\<turnstile> \<Delta>" using axioms_valid(3)[OF 4(5)] 4(2) by simp
  show ?thesis
  proof (cases "atom a = atom a'")
    case True
    then show ?thesis by (metis 4 Abs1_eq_iff(3) atom_eq_iff term_elist.eq_iff(6) that)
  next
    case False
    then have 1: "atom a \<sharp> BTyVar a' k # \<Gamma>" using b by (simp add: 4 fresh_Cons)
    have 2: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)), \<Delta> \<turnstile> (a' \<leftrightarrow> a) \<bullet> e' : (a' \<leftrightarrow> a) \<bullet> \<sigma>'" using Tm.eqvt[OF 4(5), of "(a' \<leftrightarrow> a)"] valid 4 by auto
    have "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = ((a' \<leftrightarrow> a) \<bullet> BTyVar a' k) # \<Gamma>" using 1 fresh flip_fresh_fresh b(1) by simp
    then have "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # \<Gamma>" by (simp add: flip_fresh_fresh)
    then have "BTyVar a k # \<Gamma> , \<Delta> \<turnstile> e : (a' \<leftrightarrow> a) \<bullet> \<sigma>'" using 2 swap by argo
    then show ?thesis by (metis "4"(3,4) Abs1_eq_iff(3) False \<tau>_tlist.eq_iff(5) \<tau>_tlist.fresh(5) b(2) empty_iff flip_commute insert_iff list.set(1,2) term_elist.eq_iff(6) that)
  qed
qed simp_all

lemma Ty_Forall_Inv:
  assumes a: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y (\<forall>a:k. \<sigma>) : \<tau>" and b: "atom a \<sharp> \<Gamma>"
  shows "BTyVar a k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star> \<and> \<tau> = \<star>"
proof (cases rule: Ty.cases[OF a])
  case (6 a' k' \<Gamma>' \<Delta>' \<sigma>')
  then have 1: "(BTyVar a' k # \<Gamma>) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" by simp
  have valid: "\<turnstile> \<Delta>" by (rule axioms_valid(2)[OF 1])
  have "(a' \<leftrightarrow> a) \<bullet> \<sigma>' = \<sigma>" using Abs_rename_body[of a' \<sigma>' a \<sigma>] 6(3) by auto
  then have 2: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma> : \<star>" using Ty.eqvt[OF 1, of "(a' \<leftrightarrow> a)"] valid by auto
  have 3: "((a' \<leftrightarrow> a) \<bullet> (BTyVar a' k # \<Gamma>)) = BTyVar a k # ((a' \<leftrightarrow> a) \<bullet> \<Gamma>)" using Cons_eqvt flip_fresh_fresh by force
  have 4: "(a' \<leftrightarrow> a) \<bullet> \<Gamma> = \<Gamma>" by (metis 6(1,5) CtxE(1) b context_valid_ty flip_def swap_fresh_fresh)
  show ?thesis using 2 3 4 6(4) by argo
qed simp_all

lemma Ty_Forall_Inv_2:
  assumes a: "\<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<forall> a : k . \<sigma> : k2"
  obtains a' \<sigma>' where "(\<forall> a:k. \<sigma>) = (\<forall> a':k. \<sigma>')" "BTyVar a' k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" "atom a' \<sharp> (a, \<sigma>)" "k2 = \<star>"
proof (cases rule: Ty.cases[OF a])
  case (6 a2 _ _ _ \<sigma>2)
  then obtain c::tyvar where "atom c \<sharp> (a, \<sigma>, a2, \<sigma>2, \<Gamma>)" using obtain_fresh by blast
  then have c: "atom c \<sharp> a" "atom c \<sharp> \<sigma>" "atom c \<sharp> a2" "atom c \<sharp> \<sigma>2" "atom c \<sharp> \<Gamma>" by auto
  obtain \<sigma>' where P: "(a2 \<leftrightarrow> c) \<bullet> (\<forall> a2:k. \<sigma>2) = (\<forall> c:k. \<sigma>')" using flip_fresh_fresh by force
  then have 1: "(a2 \<leftrightarrow> c) \<bullet> \<sigma>2 = \<sigma>'" by (simp add: Abs1_eq_iff(3))
  have 2: "(a2 \<leftrightarrow> c) \<bullet> \<Gamma> = \<Gamma>" by (metis 6(1,5) CtxE(1) c(5) context_valid_ty flip_def swap_fresh_fresh)
  have 3: "((a2 \<leftrightarrow> c) \<bullet> BTyVar a2 k) = BTyVar c k" using P by auto
  have valid: "\<turnstile> \<Delta>" using axioms_valid(2)[OF 6(5)] 6(2) by simp
  have "(a2 \<leftrightarrow> c) \<bullet> (BTyVar a2 k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>2 : \<star>)" using 6 by auto
  then have "((a2 \<leftrightarrow> c) \<bullet> (BTyVar a2 k # \<Gamma>)) , \<Delta> \<turnstile>\<^sub>t\<^sub>y (a2 \<leftrightarrow> c) \<bullet> \<sigma>2 : \<star>" using valid by auto
  then have "(((a2 \<leftrightarrow> c) \<bullet> BTyVar a2 k) # ((a2 \<leftrightarrow> c) \<bullet> \<Gamma>)) , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" using 1 by auto
  then have x: "BTyVar c k # \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<sigma>' : \<star>" using 2 3 by argo
  have y: "(a2 \<leftrightarrow> c) \<bullet> (\<forall> a2:k. \<sigma>2) = (\<forall> a2:k. \<sigma>2)" by (metis \<tau>_tlist.fresh(5) c(4) flip_def insert_iff list.set(2) no_tyvars_in_kinds swap_fresh_fresh)
  show ?thesis using that[OF _ x _ 6(4)] c(1,2) by (metis 6(3) P \<tau>_tlist.eq_iff(5) fresh_Pair y)
qed simp_all

lemma axiom_isin_same_kind: "\<lbrakk> AxData T k1 \<in> set (\<Delta>' @ AxData T k2 # \<Delta>) ; \<turnstile> (\<Delta>' @ AxData T k2 # \<Delta>) \<rbrakk> \<Longrightarrow> k1 = k2"
proof (induction \<Delta>')
  case Nil
  then have "atom T \<sharp> \<Delta>" by auto
  then have "\<nexists>k. AxData T k \<in> set \<Delta>" by (metis (mono_tags, lifting) axiom.fresh(1) fresh_Cons fresh_append fresh_at_base(2) in_set_conv_decomp_first)
  then show ?case using Nil.prems(1) by auto
next
  case (Cons a \<Delta>')
  then show ?case using axioms_valid(2)
  proof (cases a rule: axiom.exhaust)
    case (AxData T' k3)
    then have "atom T' \<sharp> (\<Delta>' @ AxData T k2 # \<Delta>)" using Cons(3) by auto
    then have "T' \<noteq> T" by (simp add: fresh_Cons fresh_append fresh_at_base(2))
    then show ?thesis using Cons AxData by auto
  qed fastforce
qed

lemma axiom_isin_same_type: "\<lbrakk> AxCtor D \<tau>1 \<in> set (\<Delta>' @ AxCtor D \<tau>2 # \<Delta>) ; \<turnstile> (\<Delta>' @ AxCtor D \<tau>2 # \<Delta>) \<rbrakk> \<Longrightarrow> \<tau>1 = \<tau>2"
proof (induction \<Delta>')
  case Nil
  then have "atom D \<sharp> \<Delta>" by auto
  then have "\<nexists>t. AxCtor D t \<in> set \<Delta>" by (metis (mono_tags, lifting) axiom.fresh(2) fresh_Cons fresh_append fresh_at_base(2) in_set_conv_decomp_first)
  then show ?case using Nil(1) by auto
next
  case (Cons a \<Delta>')
  then show ?case
  proof (cases a rule: axiom.exhaust)
    case (AxCtor D' \<tau>')
    then have "atom D' \<sharp> (\<Delta>' @ AxCtor D \<tau>2 # \<Delta>)" using Cons(3) by auto
    then have "D' \<noteq> D" by (simp add: fresh_Cons fresh_append fresh_at_base(2))
    then show ?thesis using AxCtor Cons axioms_valid_aux(2) set_ConsD by auto
  qed auto
qed

lemmas axiom_isin_same = axiom_isin_same_kind axiom_isin_same_type

lemma axiom_isin_split: "\<lbrakk> b \<in> set \<Delta> ; \<turnstile> \<Delta> \<rbrakk> \<Longrightarrow> \<exists>\<Delta>1 \<Delta>2. \<Delta> = \<Delta>1 @ b # \<Delta>2"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
  proof (cases "a = b")
    case True
    then show ?thesis by blast
  next
    case False
    then show ?thesis by (meson Cons.prems(1) split_list)
  qed
qed simp

lemma isin_subset:
  fixes \<Gamma>::"\<Gamma>"
  assumes "\<Delta> \<turnstile> \<Gamma>' @ \<Gamma>"
  shows "bndr \<in> \<Gamma> \<longrightarrow> bndr \<in> (\<Gamma>' @ \<Gamma>)"
proof
  assume "bndr \<in> \<Gamma>"
  then show "bndr \<in> (\<Gamma>' @ \<Gamma>)"
  using assms proof (induction \<Gamma>' arbitrary: \<Gamma>)
    case (Cons b \<Gamma>2)
    have 1: "\<Delta> \<turnstile> \<Gamma>2 @ \<Gamma>" using Cons(3) by auto
    have 2: "bndr \<in> (\<Gamma>2 @ \<Gamma>)" by (rule Cons(1)[OF Cons(2) 1])
    show ?case
    proof (cases b rule: binder.exhaust)
      case (BVar x \<tau>)
      then have "atom x \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons by auto
      then show ?thesis using 2 BVar fresh_not_isin_var by (cases bndr rule: binder.exhaust) auto
    next
      case (BTyVar a k)
      then have "atom a \<sharp> (\<Gamma>2 @ \<Gamma>)" using Cons by auto
      then show ?thesis using 2 BTyVar fresh_not_isin_tyvar by (cases bndr rule: binder.exhaust) auto
    qed
  qed auto
qed

lemma isin_superset_tyvar: "\<lbrakk> BTyVar a k \<in> (\<Gamma>' @ BVar x \<tau> # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<rbrakk> \<Longrightarrow> BTyVar a k \<in> (\<Gamma>' @ \<Gamma>)"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case by (cases bndr rule: binder.exhaust) auto
qed auto

lemma isin_superset_var: "\<lbrakk> BVar x \<tau> \<in> (\<Gamma>' @ BVar y \<tau>2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BVar y \<tau>2 # \<Gamma> ; x \<noteq> y \<rbrakk> \<Longrightarrow> BVar x \<tau> \<in> (\<Gamma>' @ \<Gamma>)"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case by (cases bndr rule: binder.exhaust) auto
qed auto
lemmas isin_superset = isin_superset_tyvar isin_superset_var

lemma isin_same_kind: "\<lbrakk> BTyVar a k1 \<in> (\<Gamma>' @ BTyVar a k2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BTyVar a k2 # \<Gamma> \<rbrakk> \<Longrightarrow> k1 = k2"
proof (induction \<Gamma>')
  case (Cons bndr \<Gamma>')
  then show ?case by (cases rule: Ctx.cases[OF Cons(3)]) (auto split: if_splits simp: fresh_Cons fresh_append fresh_at_base(2))
qed auto

lemma isin_same_type: "\<lbrakk> BVar x \<tau> \<in> (\<Gamma>' @ BVar x \<tau>2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau>2 # \<Gamma> \<rbrakk> \<Longrightarrow> \<tau> = \<tau>2"
proof (induction \<Gamma>')
  case (Cons a \<Gamma>')
  then show ?case by (cases rule: Ctx.cases[OF Cons(3)]) (auto split: if_splits simp: fresh_Cons fresh_append fresh_at_base)
qed auto
lemmas isin_same = isin_same_kind isin_same_type

lemma isin_subst_tyvar: "\<lbrakk> BTyVar a k \<in> (\<Gamma>' @ BTyVar b k2 # \<Gamma>) ; \<Delta> \<turnstile> \<Gamma>' @ BTyVar b k2 # \<Gamma> ; a \<noteq> b \<rbrakk> \<Longrightarrow> BTyVar a k \<in> (\<Gamma>'[\<sigma>/b] @ \<Gamma>)"
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

lemma context_split_valid: "(\<Delta>::\<Delta>) \<turnstile> (\<Gamma>' @ \<Gamma>) \<Longrightarrow> \<Delta> \<turnstile> \<Gamma>"
  by (induction \<Gamma>') (auto simp: Ctx_Empty)

lemma isin_split: "\<lbrakk> b \<in> \<Gamma> ; \<Delta> \<turnstile> \<Gamma> \<rbrakk> \<Longrightarrow> \<exists>\<Gamma>1 \<Gamma>2. \<Gamma> = \<Gamma>1 @ b # \<Gamma>2"
proof (induction \<Gamma>)
  case (Cons bndr \<Gamma>)
  then show ?case
  proof (cases "bndr = b")
    case False
    then have "b \<in> \<Gamma>"
    proof (cases bndr rule: binder.exhaust)
      case (BVar x \<tau>)
      then show ?thesis using False Cons by (cases b rule: binder.exhaust) auto
    next
      case (BTyVar a k)
      then show ?thesis using False Cons by (cases b rule: binder.exhaust) auto
    qed
    then show ?thesis by (metis Cons.IH Cons.prems(2) Cons_eq_appendI context_cons_valid)
  qed blast
qed auto

lemma context_regularity: "\<Delta> \<turnstile> \<Gamma>' @ BVar x \<tau> # \<Gamma> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>t\<^sub>y \<tau> : \<star>"
  using Ctx_Var context_split_valid by (induction \<Gamma>) blast+

end
