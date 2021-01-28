theory Lemmas
  imports Syntax Defs
begin

(* \<lbrakk> atom x \<sharp> t' ; x = y \<or> atom x \<sharp> t \<rbrakk> \<Longrightarrow> atom x \<sharp> t[t'/y] *)
lemma fresh_subst_term:
  assumes "atom x \<sharp> e'"
  shows "x = y \<or> atom x \<sharp> e \<Longrightarrow> atom x \<sharp> subst_term e e' y"
    and "x = y \<or> atom x \<sharp> es \<Longrightarrow> atom x \<sharp> subst_term_list es e' y"
  using assms by (nominal_induct e and es avoiding: x y e' rule: term_elist.strong_induct) auto
lemma fresh_subst_term_tyvar:
  assumes "atom (a::tyvar) \<sharp> e'"
  shows "atom a \<sharp> e \<Longrightarrow> atom a \<sharp> subst_term e e' y"
   and "atom a \<sharp> es \<Longrightarrow> atom a \<sharp> subst_term_list es e' y"
  using assms by (nominal_induct e and es avoiding: y a e' rule: term_elist.strong_induct) auto
lemma fresh_subst_type:
  assumes "atom a \<sharp> \<tau>"
  shows "a = b \<or> atom a \<sharp> \<sigma> \<Longrightarrow> atom a \<sharp> subst_type \<sigma> \<tau> b"
    and "a = b \<or> atom a \<sharp> tys \<Longrightarrow> atom a \<sharp> subst_type_list tys \<tau> b"
  using assms by (nominal_induct \<sigma> and tys avoiding: a b \<tau> rule: \<tau>_tlist.strong_induct) auto
lemma fresh_subst_term_type:
  assumes "atom a \<sharp> \<tau>"
  shows "a = b \<or> atom a \<sharp> e \<Longrightarrow> atom a \<sharp> subst_term_type e \<tau> b"
  and "a = b \<or> atom a \<sharp> es \<Longrightarrow> atom a \<sharp> subst_term_list_type es \<tau> b"
  using assms by (nominal_induct e and es avoiding: a b \<tau> rule: term_elist.strong_induct) (auto simp: fresh_subst_type)
lemma fresh_subst_context_var: "atom x \<sharp> \<Gamma> \<Longrightarrow> atom (x::var) \<sharp> subst_context \<Gamma> \<tau>' a"
  by (induction \<Gamma> \<tau>' a rule: subst_context.induct) (auto simp: fresh_Cons)
lemma fresh_subst_context_tyvar: "\<lbrakk> atom a \<sharp> \<tau>' ; a = b \<or> atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_context \<Gamma> \<tau>' b"
  by (induction \<Gamma> \<tau>' a rule: subst_context.induct) (auto simp: fresh_Cons fresh_Nil fresh_subst_type)
lemmas fresh_subst = fresh_subst_term fresh_subst_term_tyvar fresh_subst_type fresh_subst_term_type fresh_subst_context_var fresh_subst_context_tyvar

(* atom c \<sharp> t \<Longrightarrow> t[t'/x] = ((x \<leftrightarrow> c) \<bullet> t)[t'/c] *)
lemma subst_term_var_name:
  shows "atom c \<sharp> e \<Longrightarrow> subst_term e e' x = subst_term ((x \<leftrightarrow> c) \<bullet> e) e' c"
  and "atom c \<sharp> es \<Longrightarrow> subst_term_list es e' x = subst_term_list ((x \<leftrightarrow> c) \<bullet> es) e' c"
proof (nominal_induct e and es avoiding: c x e' rule: term_elist.strong_induct)
  case (Let y \<tau> e1 e2)
  then have "(Let y \<tau> e1 e2)[e'/x] = Let y \<tau> e1[e'/x] e2[e'/x]" by auto
  also have "... = Let y \<tau> ((x \<leftrightarrow> c) \<bullet> e1)[e'/c] ((x \<leftrightarrow> c) \<bullet> e2)[e'/c]"
    by (metis Let.hyps(1) Let.hyps(4) Let.hyps(5) Let.prems fresh_at_base(2) list.set(1) list.set(2) singletonD term_elist.fresh(7))
  also have "... = (Let y \<tau> ((x \<leftrightarrow> c) \<bullet> e1) ((x \<leftrightarrow> c) \<bullet> e2))[e'/c]" by (simp add: Let.hyps(1) Let.hyps(3))
  finally show ?case
    by (metis Let.hyps(1) Let.hyps(2) flip_fresh_fresh fresh_at_base(2) no_vars_in_ty term_elist.perm_simps(7))
qed (auto simp: flip_fresh_fresh fresh_at_base)

lemma subst_type_var_name:
  shows "atom c \<sharp> \<sigma> \<Longrightarrow> subst_type \<sigma> \<tau> a = subst_type ((a \<leftrightarrow> c) \<bullet> \<sigma>) \<tau> c"
    and "atom c \<sharp> tys \<Longrightarrow> subst_type_list tys \<tau> a = subst_type_list ((a \<leftrightarrow> c) \<bullet> tys) \<tau> c"
proof (nominal_induct \<sigma> and tys avoiding: c a \<tau> rule: \<tau>_tlist.strong_induct)
  case (TyForall b k \<sigma>)
  then have "(\<forall> b:k. \<sigma>)[\<tau>/a] = (\<forall> b:k. \<sigma>[\<tau>/a])" by simp
  also have "... = (\<forall> b:k. ((a \<leftrightarrow> c) \<bullet> \<sigma>)[\<tau>/c])" by (metis TyForall.hyps(1) TyForall.hyps(4) TyForall.prems \<tau>_tlist.fresh(5) fresh_at_base(2) list.set(1) list.set(2) singletonD)
  also have "... = (\<forall> b:k. ((a \<leftrightarrow> c) \<bullet> \<sigma>))[\<tau>/c]" by (simp add: TyForall.hyps(1) TyForall.hyps(3))
  finally show ?case by (metis TyForall.hyps(1) TyForall.hyps(2) \<tau>_tlist.perm_simps(5) flip_fresh_fresh fresh_at_base(2) no_tyvars_in_kinds)
qed (auto simp: fresh_at_base)

lemma subst_term_type_var_name:
  shows "atom c \<sharp> e \<Longrightarrow> subst_term_type e \<tau> a = subst_term_type ((a \<leftrightarrow> c) \<bullet> e) \<tau> c"
    and "atom c \<sharp> es \<Longrightarrow> subst_term_list_type es \<tau> a = subst_term_list_type ((a \<leftrightarrow> c) \<bullet> es) \<tau> c"
proof (nominal_induct e and es avoiding: c a \<tau> rule: term_elist.strong_induct)
  case (Lam x \<tau>1 e)
  then have "(\<lambda> x:\<tau>1. e)[\<tau>/a] = (\<lambda> x:\<tau>1[\<tau>/a]. e[\<tau>/a])" by simp
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c]. e[\<tau>/a])" using subst_type_var_name Lam by force
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c]. ((a \<leftrightarrow> c) \<bullet> e)[\<tau>/c])" using Lam by (metis fresh_at_base(2) list.set(1) list.set(2) singletonD term_elist.fresh(5))
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1). ((a \<leftrightarrow> c) \<bullet> e))[\<tau>/c]" by simp
  finally show ?case by (simp add: Lam.hyps(2) flip_fresh_fresh)
next
  case (Let x \<tau>1 e1 e2)
  then have "(Let x \<tau>1 e1 e2)[\<tau>/a] = Let x \<tau>1[\<tau>/a] e1[\<tau>/a] e2[\<tau>/a]" by simp
  also have "... = Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c] e1[\<tau>/a] e2[\<tau>/a]" using subst_type_var_name Let by auto
  also have "... = Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c] ((a \<leftrightarrow> c) \<bullet> e1)[\<tau>/c] ((a \<leftrightarrow> c) \<bullet> e2)[\<tau>/c]"
    by (metis (mono_tags, lifting) Let.hyps(1) Let.hyps(4) Let.hyps(5) Let.prems fresh_at_base(2) list.set(1) list.set(2) singletonD term_elist.fresh(7))
  also have "... = (Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1) ((a \<leftrightarrow> c) \<bullet> e1) ((a \<leftrightarrow> c) \<bullet> e2))[\<tau>/c]" by simp
  finally show ?case by (simp add: flip_fresh_fresh)
qed (auto simp: flip_fresh_fresh fresh_at_base subst_type_var_name)

lemma subst_context_var_name: "atom c \<sharp> \<Gamma> \<Longrightarrow> subst_context \<Gamma> \<tau> a = subst_context ((a \<leftrightarrow> c) \<bullet> \<Gamma>) \<tau> c"
proof (induction \<Gamma> \<tau> a rule: subst_context.induct)
  case (3 b k \<Gamma> \<tau>' a)
  then have 1: "\<Gamma>[\<tau>'/a] = ((a \<leftrightarrow> c) \<bullet> \<Gamma>)[\<tau>'/c]" by (auto simp: fresh_Cons)
  have 2: "b \<noteq> c" using 3 binder.fresh(2) fresh_Cons fresh_at_base(2) by blast
  then show ?case
  proof (cases "a = b")
    case True
    then show ?thesis using 1 by auto
  next
    case False
    then have a: "(BTyVar b k # \<Gamma>)[\<tau>'/a] = BTyVar b k # \<Gamma>[\<tau>'/a]" by simp
    from False have b: "((a \<leftrightarrow> c) \<bullet> (BTyVar b k # \<Gamma>))[\<tau>'/c] = ((a \<leftrightarrow> c) \<bullet> BTyVar b k) # ((a \<leftrightarrow> c) \<bullet> \<Gamma>)[\<tau>'/c]" using flip_fresh_fresh 2 by simp
    have c: "(a \<leftrightarrow> c) \<bullet> BTyVar b k = BTyVar b k" using False 2 flip_fresh_fresh by force
    show ?thesis using a b c 1 by argo
  qed
qed (auto simp: flip_fresh_fresh fresh_Cons subst_type_var_name)
lemmas subst_var_name = subst_term_var_name subst_type_var_name subst_term_type_var_name subst_context_var_name

(* [[atom a]]lst. t = [[atom a2]]lst. t2 \<Longrightarrow> subst t t' a = subst t2 t' a2 *)
lemma subst_term_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term e t a = subst_term e' t a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_var_name(1))
lemma subst_term_list_same: "[[atom a]]lst. es = [[atom a']]lst. es' \<Longrightarrow> subst_term_list es t a = subst_term_list es' t a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_var_name(2))
lemma subst_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_type e \<tau> a = subst_type e' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_type_var_name(1))
lemma subst_type_list_same: "[[atom a]]lst. es = [[atom a']]lst. es' \<Longrightarrow> subst_type_list es \<tau> a = subst_type_list es' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_type_var_name(2))
lemma subst_term_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term_type e \<tau> a = subst_term_type e' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_type_var_name(1))
lemma subst_term_list_type_same: "[[atom a]]lst. es = [[atom a']]lst. es' \<Longrightarrow> subst_term_list_type es \<tau> a = subst_term_list_type es' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_type_var_name(2))
lemmas subst_same = subst_term_same subst_term_list_same subst_type_same subst_type_list_same subst_term_type_same subst_term_list_type_same

(* atom x \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (B x _) \<Gamma> *)
lemma fresh_not_isin_tyvar: "atom a \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (BTyVar a k) \<Gamma>"
  apply (induction \<Gamma>) apply simp
  by (metis binder.fresh(2) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(4) isin.simps(5))
lemma fresh_not_isin_var: "atom x \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (BVar x \<tau>) \<Gamma>"
  apply (induction \<Gamma>) apply simp
  by (metis (mono_tags, lifting) binder.fresh(1) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(2) isin.simps(3))

(* atom x \<sharp> t \<Longrightarrow> subst t' x t = t *)
lemma fresh_subst_term_same:
  shows "atom x \<sharp> e \<Longrightarrow> subst_term e e' x = e"
  and "atom x \<sharp> es \<Longrightarrow> subst_term_list es e' x = es"
proof (induction e e' x and es e' x rule: subst_term_subst_term_list.induct)
  case (5 y e x \<tau> e2)
  then show ?case using fresh_PairD(2) fresh_at_base(2) by fastforce
next
  case (7 y e x \<tau> e1 e2)
  then show ?case using fresh_PairD(2) fresh_at_base(2) by fastforce
qed auto
lemma fresh_subst_type_same:
  shows "atom a \<sharp> \<sigma> \<Longrightarrow> subst_type \<sigma> \<tau> a = \<sigma>"
  and "atom a \<sharp> tys \<Longrightarrow> subst_type_list tys \<tau> a = tys"
proof (induction \<sigma> \<tau> a and tys \<tau> a rule: subst_type_subst_type_list.induct)
  case (5 b \<tau> a k \<sigma>)
  then show ?case using fresh_Pair fresh_at_base(2) fresh_def list.set(1) list.set(2) subst_type.simps(4) by fastforce
qed auto
lemma fresh_subst_term_type_same:
  shows "atom a \<sharp> e \<Longrightarrow> subst_term_type e \<tau> a = e"
    and "atom a \<sharp> es \<Longrightarrow> subst_term_list_type es \<tau> a = es"
proof (induction e \<tau> a and es \<tau> a rule: subst_term_type_subst_term_list_type.induct)
  case (6 b \<tau> a k e2)
  then show ?case by (simp add: "6.hyps" fresh_Pair fresh_at_base(2))
qed (auto simp: fresh_subst_type_same)
lemma fresh_subst_context_same: "atom a \<sharp> \<Gamma> \<Longrightarrow> subst_context \<Gamma> \<tau> a = \<Gamma>"
  by (induction \<Gamma> \<tau> a rule: subst_context.induct) (auto simp: fresh_Cons fresh_subst_type_same)
lemmas fresh_subst_same = fresh_subst_term_same fresh_subst_type_same fresh_subst_term_type_same fresh_subst_context_same

(* \<lbrakk> x \<noteq> y ; atom x \<sharp> t1 \<rbrakk> \<Longrightarrow> subst (subst e t2 x) t1 y = subst (subst e t1 y) (subst t2 t1 y) x *)
lemma subst_subst_term:
  assumes "x \<noteq> y" "atom x \<sharp> t1"
  shows "subst_term (subst_term e t2 x) t1 y = subst_term (subst_term e t1 y) (subst_term t2 t1 y) x"
  and "subst_term_list (subst_term_list es t2 x) t1 y = subst_term_list (subst_term_list es t1 y) (subst_term t2 t1 y) x"
using assms by (nominal_induct e and es avoiding: x y t1 t2 rule: term_elist.strong_induct) (auto simp: fresh_subst_same fresh_subst)
lemma subst_subst_type:
  assumes "a \<noteq> b" "atom a \<sharp> \<tau>1"
  shows "subst_type (subst_type \<sigma> \<tau>2 a) \<tau>1 b = subst_type (subst_type \<sigma> \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
    and "subst_type_list (subst_type_list tys \<tau>2 a) \<tau>1 b = subst_type_list (subst_type_list tys \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
using assms by (nominal_induct \<sigma> and tys avoiding: a b \<tau>1 \<tau>2 rule: \<tau>_tlist.strong_induct) (auto simp: fresh_subst_same fresh_subst)
lemma subst_subst_term_type:
  assumes "a \<noteq> b" "atom a \<sharp> \<tau>1"
  shows "subst_term_type (subst_term_type e \<tau>2 a) \<tau>1 b = subst_term_type (subst_term_type e \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
    and "subst_term_list_type (subst_term_list_type es \<tau>2 a) \<tau>1 b = subst_term_list_type (subst_term_list_type es \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
using assms by (nominal_induct e and es avoiding: a b \<tau>1 \<tau>2 rule: term_elist.strong_induct) (auto simp: fresh_subst_same fresh_subst subst_subst_type)
lemma subst_subst_context: "\<lbrakk> a \<noteq> b; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_context (subst_context \<Gamma> \<tau>2 a) \<tau>1 b = subst_context (subst_context \<Gamma> \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
  by (induction \<Gamma> \<tau>2 a rule: subst_context.induct) (auto simp: subst_subst_type)
lemmas subst_subst = subst_subst_term subst_subst_type subst_subst_term_type subst_subst_context

(* misc *)
lemma fv_supp_subset: shows "fv_\<tau> \<tau> \<subseteq> supp \<tau>" and "fv_tlist tys \<subseteq> supp tys"
  by (induction \<tau> and tys rule: \<tau>_tlist.inducts) (auto simp: \<tau>_tlist.supp \<tau>_tlist.fv_defs)

end
