theory Lemmas
  imports Syntax Defs
begin

lemma fresh_match_Pair:
  fixes tys::"tyvar list" and vals::"var list"
  assumes "set (map atom tys) \<sharp>* e" "set (map atom vals) \<sharp>* e" "set (map atom tys) \<sharp>* y"  "set (map atom vals) \<sharp>* y"
  shows "set (map atom tys @ map atom vals) \<sharp>* (e, y)"
  by (metis assms fresh_star_Pair fresh_star_Un set_append)

lemma fresh_in_match_var:
  fixes x::"var"
  assumes "set (map atom tys) \<sharp>* x" "set (map atom vals) \<sharp>* x" "atom x \<sharp> MatchCtor D tys vals e"
  shows "atom x \<sharp> e"
  using assms fresh_at_base(2) fresh_star_Un fresh_star_def by fastforce

lemma fresh_in_match_tyvar:
  fixes a::"tyvar"
  assumes "set (map atom tys) \<sharp>* a" "set (map atom vals) \<sharp>* a" "atom a \<sharp> MatchCtor D tys vals e"
  shows "atom a \<sharp> e"
  using assms fresh_at_base(2) fresh_star_Un fresh_star_def by fastforce
lemmas fresh_in_match = fresh_in_match_var fresh_in_match_tyvar

lemma fresh_star_invert: "set (map atom xs) \<sharp>* a \<Longrightarrow> atom a \<sharp> xs"
  unfolding fresh_star_def by (induction xs) (auto simp: fresh_Cons fresh_Nil fresh_at_base(2))

lemma match_ctor_eqvt_var:
  fixes a c::"var"
  assumes "set (map atom tys) \<sharp>* a" "set (map atom vals) \<sharp>* a" "set (map atom tys) \<sharp>* c" "set (map atom vals) \<sharp>* c"
  shows "(a \<leftrightarrow> c) \<bullet> MatchCtor D tys vals e = MatchCtor D tys vals ((a \<leftrightarrow> c) \<bullet> e)"
proof -
  from assms(1,3) have 1: "(a \<leftrightarrow> c) \<bullet> tys = tys" using fresh_star_invert flip_fresh_fresh by blast
  from assms(2,4) have 2: "(a \<leftrightarrow> c) \<bullet> vals = vals" using fresh_star_invert flip_fresh_fresh by blast
  from 1 2 show ?thesis by auto
qed

lemma match_ctor_eqvt_tyvar:
  fixes a c::"tyvar"
  assumes "set (map atom tys) \<sharp>* a" "set (map atom vals) \<sharp>* a" "set (map atom tys) \<sharp>* c" "set (map atom vals) \<sharp>* c"
  shows "(a \<leftrightarrow> c) \<bullet> MatchCtor D tys vals e = MatchCtor D tys vals ((a \<leftrightarrow> c) \<bullet> e)"
proof -
  from assms(1,3) have 1: "(a \<leftrightarrow> c) \<bullet> tys = tys" using fresh_star_invert flip_fresh_fresh by blast
  from assms(2,4) have 2: "(a \<leftrightarrow> c) \<bullet> vals = vals" using fresh_star_invert flip_fresh_fresh by blast
  from 1 2 show ?thesis by auto
qed
lemmas match_ctor_eqvt = match_ctor_eqvt_var match_ctor_eqvt_tyvar

(* \<lbrakk> atom x \<sharp> t' ; x = y \<or> atom x \<sharp> t \<rbrakk> \<Longrightarrow> atom x \<sharp> t[t'/y] *)
lemma fresh_subst_term:
  shows "\<lbrakk> atom x \<sharp> e' ; x = y \<or> atom x \<sharp> e \<rbrakk> \<Longrightarrow> atom x \<sharp> subst_term e e' y"
  and "\<lbrakk> atom x \<sharp> e' ; x = y \<or> atom x \<sharp> alts \<rbrakk> \<Longrightarrow> atom x \<sharp> subst_alt_list alts e' y"
  and "\<lbrakk> atom x \<sharp> e' ; x = y \<or> atom x \<sharp> alt \<rbrakk> \<Longrightarrow> atom x \<sharp> subst_alt alt e' y"
proof (nominal_induct e and alts and alt avoiding: x y e' rule: term_alt_list_alt.strong_induct)
  case (MatchCtor D tys vals e)
  then have "atom x \<sharp> e[e'/y]" using fresh_in_match(1) by blast
  then show ?case using fresh_match_Pair[OF MatchCtor(3,6,2,5)] by simp
qed auto
lemma fresh_subst_term_tyvar:
  shows "\<lbrakk> atom (a::tyvar) \<sharp> e' ; atom a \<sharp> e \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_term e e' y"
  and "\<lbrakk> atom (a::tyvar) \<sharp> e' ; atom a \<sharp> alts \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_alt_list alts e' y"
  and "\<lbrakk> atom (a::tyvar) \<sharp> e' ; atom a \<sharp> alt \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_alt alt e' y"
proof (nominal_induct e and alts and alt avoiding: a y e' rule: term_alt_list_alt.strong_induct)
  case (MatchCtor D tys vals e)
  then have "atom a \<sharp> e[e'/y]" using fresh_in_match(2) by blast
  then show ?case using fresh_match_Pair[OF MatchCtor(3,6,2,5)] by simp
qed auto
lemma fresh_subst_type: "\<lbrakk> atom a \<sharp> \<tau> ; a = b \<or> atom a \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_type \<sigma> \<tau> b"
  by (nominal_induct \<sigma> avoiding: a b \<tau> rule: \<tau>.strong_induct) auto
lemma fresh_subst_term_type:
  shows "\<lbrakk> atom a \<sharp> \<tau> ; a = b \<or> atom a \<sharp> e \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_term_type e \<tau> b"
  and "\<lbrakk> atom a \<sharp> \<tau> ; a = b \<or> atom a \<sharp> alts \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_alt_list_type alts \<tau> b"
  and "\<lbrakk> atom a \<sharp> \<tau> ; a = b \<or> atom a \<sharp> alt \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_alt_type alt \<tau> b"
proof (nominal_induct e and alts and alt avoiding: a b \<tau> rule: term_alt_list_alt.strong_induct)
  case (MatchCtor D tys vals e)
  then have "atom a \<sharp> e[\<tau>/b]" using fresh_in_match(2) by blast
  then show ?case using fresh_match_Pair[OF MatchCtor(3,6,2,5)] by simp
qed (auto simp: fresh_subst_type)
lemma fresh_subst_context_var: "atom x \<sharp> \<Gamma> \<Longrightarrow> atom (x::var) \<sharp> subst_context \<Gamma> \<tau>' a"
  by (induction \<Gamma> \<tau>' a rule: subst_context.induct) (auto simp: fresh_Cons)
lemma fresh_subst_context_tyvar: "\<lbrakk> atom a \<sharp> \<tau>' ; a = b \<or> atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_context \<Gamma> \<tau>' b"
  by (induction \<Gamma> \<tau>' a rule: subst_context.induct) (auto simp: fresh_Cons fresh_Nil fresh_subst_type)
lemmas fresh_subst = fresh_subst_term(1) fresh_subst_term_tyvar(1) fresh_subst_type fresh_subst_term_type(1) fresh_subst_context_var fresh_subst_context_tyvar fresh_subst_term(2,3) fresh_subst_term_tyvar(2,3) fresh_subst_term_type(2,3)

(* atom c \<sharp> t \<Longrightarrow> t[t'/x] = ((x \<leftrightarrow> c) \<bullet> t)[t'/c] *)
lemma subst_term_var_name:
  shows "atom c \<sharp> e \<Longrightarrow> subst_term e e' x = subst_term ((x \<leftrightarrow> c) \<bullet> e) e' c"
  and "atom c \<sharp> alts \<Longrightarrow> subst_alt_list alts e' x = subst_alt_list ((x \<leftrightarrow> c) \<bullet> alts) e' c"
  and "atom c \<sharp> alt \<Longrightarrow> subst_alt alt e' x = subst_alt ((x \<leftrightarrow> c) \<bullet> alt) e' c"
proof (nominal_induct e and alts and alt avoiding: c x e' rule: term_alt_list_alt.strong_induct)
  case (Let y \<tau> e1 e2)
  then have "(Let y \<tau> e1 e2)[e'/x] = Let y \<tau> e1[e'/x] e2[e'/x]" by auto
  also have "... = Let y \<tau> ((x \<leftrightarrow> c) \<bullet> e1)[e'/c] ((x \<leftrightarrow> c) \<bullet> e2)[e'/c]"
    by (metis Let.hyps(1) Let.hyps(4) Let.hyps(5) Let.prems fresh_at_base(2) list.set(1) list.set(2) singletonD term_alt_list_alt.fresh(7))
  also have "... = (Let y \<tau> ((x \<leftrightarrow> c) \<bullet> e1) ((x \<leftrightarrow> c) \<bullet> e2))[e'/c]" by (simp add: Let.hyps(1) Let.hyps(3))
  finally show ?case
    by (metis Let.hyps(1) Let.hyps(2) flip_fresh_fresh fresh_at_base(2) no_vars_in_ty term_alt_list_alt.perm_simps(7))
next
  case (MatchCtor D tys vals e)
  from MatchCtor have "(MatchCtor D tys vals e)[e'/x] = MatchCtor D tys vals e[e'/x]" using fresh_match_Pair[OF MatchCtor(3,6,2,5)] by auto
  also have "... = MatchCtor D tys vals ((x \<leftrightarrow> c) \<bullet> e)[e'/c]" using fresh_in_match(1) MatchCtor by metis
  also have "... = (MatchCtor D tys vals ((x \<leftrightarrow> c) \<bullet> e))[e'/c]" using fresh_match_Pair[OF MatchCtor(3,6,1,4)] by simp
  finally show ?case using match_ctor_eqvt(1)[OF MatchCtor(2,5,1,4)] by presburger
qed (auto simp: flip_fresh_fresh fresh_at_base)

lemma subst_type_var_name: "atom c \<sharp> \<sigma> \<Longrightarrow> subst_type \<sigma> \<tau> a = subst_type ((a \<leftrightarrow> c) \<bullet> \<sigma>) \<tau> c"
proof (nominal_induct \<sigma> avoiding: c a \<tau> rule: \<tau>.strong_induct)
  case (TyForall b k \<sigma>)
  then have "(\<forall> b:k. \<sigma>)[\<tau>/a] = (\<forall> b:k. \<sigma>[\<tau>/a])" by simp
  also have "... = (\<forall> b:k. ((a \<leftrightarrow> c) \<bullet> \<sigma>)[\<tau>/c])" by (metis TyForall.hyps(1) TyForall.hyps(4) TyForall.prems \<tau>.fresh(5) fresh_at_base(2) list.set(1) list.set(2) singletonD)
  also have "... = (\<forall> b:k. ((a \<leftrightarrow> c) \<bullet> \<sigma>))[\<tau>/c]" by (simp add: TyForall.hyps(1) TyForall.hyps(3))
  finally show ?case by (metis TyForall.hyps(1) TyForall.hyps(2) \<tau>.perm_simps(5) flip_fresh_fresh fresh_at_base(2) no_tyvars_in_kinds)
qed (auto simp: fresh_at_base)

lemma subst_term_type_var_name:
  shows "atom c \<sharp> e \<Longrightarrow> subst_term_type e \<tau> a = subst_term_type ((a \<leftrightarrow> c) \<bullet> e) \<tau> c"
  and "atom c \<sharp> alts \<Longrightarrow> subst_alt_list_type alts \<tau> a = subst_alt_list_type ((a \<leftrightarrow> c) \<bullet> alts) \<tau> c"
  and "atom c \<sharp> alt \<Longrightarrow> subst_alt_type alt \<tau> a = subst_alt_type ((a \<leftrightarrow> c) \<bullet> alt) \<tau> c"
proof (nominal_induct e and alts and alt avoiding: c a \<tau> rule: term_alt_list_alt.strong_induct)
  case (Lam x \<tau>1 e)
  then have "(\<lambda> x:\<tau>1. e)[\<tau>/a] = (\<lambda> x:\<tau>1[\<tau>/a]. e[\<tau>/a])" by simp
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c]. e[\<tau>/a])" using subst_type_var_name Lam by force
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c]. ((a \<leftrightarrow> c) \<bullet> e)[\<tau>/c])" using Lam by (metis fresh_at_base(2) list.set(1) list.set(2) singletonD term_alt_list_alt.fresh(5))
  also have "... = (\<lambda> x:((a \<leftrightarrow> c) \<bullet> \<tau>1). ((a \<leftrightarrow> c) \<bullet> e))[\<tau>/c]" by simp
  finally show ?case by (simp add: Lam.hyps(2) flip_fresh_fresh)
next
  case (Let x \<tau>1 e1 e2)
  then have "(Let x \<tau>1 e1 e2)[\<tau>/a] = Let x \<tau>1[\<tau>/a] e1[\<tau>/a] e2[\<tau>/a]" by simp
  also have "... = Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c] e1[\<tau>/a] e2[\<tau>/a]" using subst_type_var_name Let by auto
  also have "... = Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1)[\<tau>/c] ((a \<leftrightarrow> c) \<bullet> e1)[\<tau>/c] ((a \<leftrightarrow> c) \<bullet> e2)[\<tau>/c]"
    by (metis (mono_tags, lifting) Let.hyps(1) Let.hyps(4) Let.hyps(5) Let.prems fresh_at_base(2) list.set(1) list.set(2) singletonD term_alt_list_alt.fresh(7))
  also have "... = (Let x ((a \<leftrightarrow> c) \<bullet> \<tau>1) ((a \<leftrightarrow> c) \<bullet> e1) ((a \<leftrightarrow> c) \<bullet> e2))[\<tau>/c]" by simp
  finally show ?case by (simp add: flip_fresh_fresh)
next
  case (MatchCtor D tys vals e)
  have "(MatchCtor D tys vals e)[\<tau>/a] = MatchCtor D tys vals e[\<tau>/a]" using fresh_match_Pair[OF MatchCtor(3,6,2,5)] by simp
  also have "... = MatchCtor D tys vals ((a \<leftrightarrow> c) \<bullet> e)[\<tau>/c]" using fresh_in_match(2) MatchCtor by metis
  also have "... = (MatchCtor D tys vals ((a \<leftrightarrow> c) \<bullet> e))[\<tau>/c]" using fresh_match_Pair[OF MatchCtor(3,6,1,4)] by simp
  finally show ?case using match_ctor_eqvt(2)[OF MatchCtor(2,5,1,4)] by presburger
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
lemmas subst_var_name = subst_term_var_name(1) subst_type_var_name subst_term_type_var_name(1) subst_context_var_name subst_term_var_name(2,3) subst_term_type_var_name(2,3)

(* [[atom a]]lst. t = [[atom a2]]lst. t2 \<Longrightarrow> subst t t' a = subst t2 t' a2 *)
lemma subst_term_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term e t a = subst_term e' t a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_var_name(1))
lemma subst_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_type e \<tau> a = subst_type e' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_type_var_name)
lemma subst_term_type_same: "[[atom a]]lst. e = [[atom a']]lst. e' \<Longrightarrow> subst_term_type e \<tau> a = subst_term_type e' \<tau> a'"
  by (metis Abs1_eq_iff(3) flip_commute subst_term_type_var_name(1))
lemmas subst_same = subst_term_same subst_type_same subst_term_type_same

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
  and "atom x \<sharp> alts \<Longrightarrow> subst_alt_list alts e' x = alts"
  and "atom x \<sharp> alt \<Longrightarrow> subst_alt alt e' x = alt"
proof (induction e e' x and alts e' x and alt e' x rule: subst_term_subst_alt_list_subst_alt.induct)
  case (6 y e x \<tau> e2)
  then show ?case using fresh_PairD(2) fresh_at_base(2) by fastforce
next
  case (8 y e x \<tau> e1 e2)
  then show ?case using fresh_PairD(2) fresh_at_base(2) by fastforce
next
  case (11 tys vals e x D t)
  then have "atom x \<sharp> t" by (meson fresh_PairD(2) fresh_at_base(2) fresh_star_def term_alt_list_alt.fresh(11))
  then show ?case using 11 by simp
qed auto

lemma fresh_subst_type_same: "atom a \<sharp> \<sigma> \<Longrightarrow> subst_type \<sigma> \<tau> a = \<sigma>"
proof (induction \<sigma> \<tau> a rule: subst_type.induct)
  case (5 b \<tau> a k \<sigma>)
  then show ?case
    using fresh_Pair fresh_at_base(2) fresh_def list.set(1) list.set(2) subst_type.simps(4) by fastforce
qed auto

lemma fresh_subst_term_type_same:
  shows "atom a \<sharp> e \<Longrightarrow> subst_term_type e \<tau> a = e"
  and "atom a \<sharp> alts \<Longrightarrow> subst_alt_list_type alts \<tau> a = alts"
  and "atom a \<sharp> alt \<Longrightarrow> subst_alt_type alt \<tau> a = alt"
proof (induction e \<tau> a and alts \<tau> a and alt \<tau> a rule: subst_term_type_subst_alt_list_type_subst_alt_type.induct)
  case (7 b \<tau> a k e2)
  then show ?case by (simp add: "7.hyps" fresh_Pair fresh_at_base(2))
next
  case (11 tys vals \<tau> a D e)
  then have "atom a \<sharp> e" by (meson fresh_PairD(2) fresh_at_base(2) fresh_star_def term_alt_list_alt.fresh(11))
  then show ?case using 11 by auto
qed (auto simp: fresh_subst_type_same)

lemma fresh_subst_context_same: "atom a \<sharp> \<Gamma> \<Longrightarrow> subst_context \<Gamma> \<tau> a = \<Gamma>"
  by (induction \<Gamma> \<tau> a rule: subst_context.induct) (auto simp: fresh_Cons fresh_subst_type_same)

lemmas fresh_subst_same = fresh_subst_term_same(1) fresh_subst_type_same fresh_subst_term_type_same(1) fresh_subst_context_same fresh_subst_term_same(2,3) fresh_subst_term_type_same(2,3)

(* \<lbrakk> x \<noteq> y ; atom x \<sharp> t1 \<rbrakk> \<Longrightarrow> subst (subst e t2 x) t1 y = subst (subst e t1 y) (subst t2 t1 y) x *)
lemma subst_subst_term:
  shows "\<lbrakk> x \<noteq> y ; atom x \<sharp> t1 \<rbrakk> \<Longrightarrow> subst_term (subst_term e t2 x) t1 y = subst_term (subst_term e t1 y) (subst_term t2 t1 y) x"
  and "\<lbrakk> x \<noteq> y ; atom x \<sharp> t1 \<rbrakk> \<Longrightarrow> subst_alt_list (subst_alt_list alts t2 x) t1 y = subst_alt_list (subst_alt_list alts t1 y) (subst_term t2 t1 y) x"
  and "\<lbrakk> x \<noteq> y ; atom x \<sharp> t1 \<rbrakk> \<Longrightarrow> subst_alt (subst_alt alt t2 x) t1 y = subst_alt (subst_alt alt t1 y) (subst_term t2 t1 y) x"
proof (nominal_induct e and alts and alt avoiding: x y t1 t2 rule: term_alt_list_alt.strong_induct)
  case (MatchCtor D tys vals e)
  have 1: "set (map atom tys) \<sharp>* t2[t1/y]" unfolding fresh_star_def using fresh_subst(2) by (metis MatchCtor(3,4) ex_map_conv fresh_star_def)
  have 2: "set (map atom vals) \<sharp>* t2[t1/y]" unfolding fresh_star_def using fresh_subst(1) by (metis MatchCtor(7,8) ex_map_conv fresh_star_def)
  have "(MatchCtor D tys vals e)[t2/x][t1/y] = MatchCtor D tys vals e[t2/x][t1/y]" using fresh_match_Pair[OF MatchCtor(4,8,1,5)] fresh_match_Pair[OF MatchCtor(3,7,2,6)] by simp
  also have "... = MatchCtor D tys vals e[t1/y][t2[t1/y]/x]" using MatchCtor by simp
  finally show ?case using fresh_match_Pair[OF MatchCtor(3,7,2,6)] fresh_match_Pair[OF 1 2 MatchCtor(1,5)] by simp
qed (auto simp: fresh_subst_same fresh_subst)
lemma subst_subst_type: "\<lbrakk> a \<noteq> b ; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_type (subst_type \<sigma> \<tau>2 a) \<tau>1 b = subst_type (subst_type \<sigma> \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
  by (nominal_induct \<sigma> avoiding: a b \<tau>1 \<tau>2 rule: \<tau>.strong_induct) (auto simp: fresh_subst_same fresh_subst)
lemma subst_subst_term_type:
  shows "\<lbrakk> a \<noteq> b ; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_term_type (subst_term_type e \<tau>2 a) \<tau>1 b = subst_term_type (subst_term_type e \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
  and "\<lbrakk> a \<noteq> b ; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_alt_list_type (subst_alt_list_type alts \<tau>2 a) \<tau>1 b = subst_alt_list_type (subst_alt_list_type alts \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
  and "\<lbrakk> a \<noteq> b ; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_alt_type (subst_alt_type alt \<tau>2 a) \<tau>1 b = subst_alt_type (subst_alt_type alt \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
proof (nominal_induct e and alts and alt avoiding: a b \<tau>1 \<tau>2 rule: term_alt_list_alt.strong_induct)
  case (MatchCtor D tys vals e)
  have 1: "set (map atom tys) \<sharp>* \<tau>2[\<tau>1/b]" unfolding fresh_star_def using fresh_subst(3) by (metis MatchCtor(3,4) ex_map_conv fresh_star_def)
  have 2: "set (map atom vals) \<sharp>* \<tau>2[\<tau>1/b]" unfolding fresh_star_def by simp
  have "(MatchCtor D tys vals e)[\<tau>2/a][\<tau>1/b] = MatchCtor D tys vals e[\<tau>2/a][\<tau>1/b]" using fresh_match_Pair[OF MatchCtor(4,8,1,5)] fresh_match_Pair[OF MatchCtor(3,7,2,6)] by simp
  also have "... = MatchCtor D tys vals e[\<tau>1/b][\<tau>2[\<tau>1/b]/a]" using MatchCtor by simp
  finally show ?case using fresh_match_Pair[OF MatchCtor(3,7,2,6)] fresh_match_Pair[OF 1 2 MatchCtor(1,5)] by simp
qed (auto simp: fresh_subst_same fresh_subst subst_subst_type)
lemma subst_subst_context: "\<lbrakk> a \<noteq> b; atom a \<sharp> \<tau>1 \<rbrakk> \<Longrightarrow> subst_context (subst_context \<Gamma> \<tau>2 a) \<tau>1 b = subst_context (subst_context \<Gamma> \<tau>1 b) (subst_type \<tau>2 \<tau>1 b) a"
  by (induction \<Gamma> \<tau>2 a rule: subst_context.induct) (auto simp: subst_subst_type)
lemmas subst_subst = subst_subst_term(1) subst_subst_type subst_subst_term_type(1) subst_subst_context subst_subst_term(2,3) subst_subst_term_type(2,3)

(* misc *)
lemma fv_supp_subset: "fv_\<tau> \<tau> \<subseteq> supp \<tau>"
  by (induction \<tau> rule: \<tau>.induct) (auto simp: \<tau>.supp \<tau>.fv_defs)

lemma head_ctor_is_value: "head_ctor e \<Longrightarrow> is_value e"
  by (induction e rule: term_alt_list_alt.inducts(1)) auto

lemma strengthen_isin_tyvar: "isin (BTyVar a k) (\<Gamma>' @ BVar x \<tau> # \<Gamma>) \<Longrightarrow> isin (BTyVar a k) (\<Gamma>' @ \<Gamma>)"
proof (induction \<Gamma>')
  case (Cons a \<Gamma>')
  then show ?case by (cases a rule: binder.exhaust) auto
qed auto

lemma isin_split: "isin bndr \<Gamma> \<Longrightarrow> \<exists>\<Gamma>1 \<Gamma>2. \<Gamma> = \<Gamma>1 @ bndr # \<Gamma>2"
proof (induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case
  proof (cases "a = bndr")
    case True
    then show ?thesis by blast
  next
    case False
    then have "isin bndr \<Gamma>" using Cons(2)
      by (cases a rule: binder.exhaust; cases bndr rule: binder.exhaust) auto
    then show ?thesis using Cons(1) by (metis Cons_eq_appendI)
  qed
qed simp

lemma supp_subst_type: "supp (subst_type \<tau> \<sigma> a) \<subseteq> (supp \<tau> - {atom a}) \<union> supp \<sigma>"
proof (induction \<tau> \<sigma> a rule: subst_type.induct)
  case (2 b \<tau> a)
  then show ?case by (cases "b = a") (auto simp: supp_at_base \<tau>.supp(1))
qed (auto simp: \<tau>.supp pure_supp)

lemma supp_head_data: "head_data \<tau> = Some (T, \<sigma>s) \<Longrightarrow> supp \<sigma>s \<subseteq> supp \<tau>"
proof (induction \<tau> arbitrary: \<sigma>s rule: head_data.induct)
  case (2 T)
  then show ?case using \<tau>.supp(2) pure_supp supp_Nil by auto
next
  case (4 \<tau>1 \<tau>2)
  then obtain xs where P: "head_data \<tau>1 = Some (T, xs)" by (auto split!: option.splits)
  then have 1: "supp xs \<subseteq> supp \<tau>1" by (rule 4(1))
  from 4(2) P have "\<sigma>s = xs @ [\<tau>2]" by auto
  then show ?case using 1 supp_append supp_Nil supp_Cons unfolding \<tau>.supp(4) by blast
qed auto

lemma supp_zip_with_var: "supp (zip_with BVar vals args) \<subseteq> supp vals \<union> supp args"
proof (induction vals arbitrary: args)
  case Nil
  then show ?case using supp_Nil by auto
next
  case (Cons a vals)
  then show ?case by (cases args) (auto simp: supp_Nil supp_Cons binder.supp)
qed

lemma supp_zip_with_tyvar: "supp (zip_with BTyVar tys ks) \<subseteq> supp tys \<union> supp ks"
proof (induction tys arbitrary: ks)
  case Nil
  then show ?case using supp_Nil by auto
next
  case (Cons a vals)
  then show ?case by (cases ks) (auto simp: supp_Nil supp_Cons binder.supp)
qed
lemmas supp_zip_with = supp_zip_with_var supp_zip_with_tyvar

lemma supp_vars: "supp (vars::var list) = set (map atom vars)"
  by (induction vars) (auto simp: supp_Nil supp_Cons supp_at_base)
lemma supp_tyvars: "supp (tyvars::tyvar list) = set (map atom tyvars)"
  by (induction tyvars) (auto simp: supp_Nil supp_Cons supp_at_base)

end
