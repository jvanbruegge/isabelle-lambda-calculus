theory Nominal2_Lemmas
  imports Main "Nominal2.Nominal2"
begin

lemma Abs_lst_rename:
  fixes a c::"'a::at" and e::"'e::fs"
  assumes "atom c \<sharp> e"
  shows "[[atom a]]lst. e = [[atom c]]lst. (a \<leftrightarrow> c) \<bullet> e"
proof -
  from assms have 1: "atom c \<notin> supp e - set [atom a]" by (simp add: fresh_def)
  have 2: "atom a \<notin> supp e - set [atom a]" by simp
  show ?thesis using Abs_swap2[OF 2 1] by (simp add: flip_def)
qed

lemma eqvt_at_deep:
  assumes fresh: "atom a \<sharp> (e, x)" "atom c \<sharp> (e, x)"
  and eqvt_at: "eqvt_at f (e2, e, x)"
shows "(a \<leftrightarrow> c) \<bullet> f (e2, e, x) = f ((a \<leftrightarrow> c) \<bullet> e2, e, x)"
proof -
  have 1: "(a \<leftrightarrow> c) \<bullet> f (e2, e, x) = f ((a \<leftrightarrow> c) \<bullet> (e2, e, x))" using eqvt_at eqvt_at_def by blast
  have 2: "(a \<leftrightarrow> c) \<bullet> (e2, e, x) = ((a \<leftrightarrow> c) \<bullet> e2, e, x)" using fresh fresh_Pair flip_fresh_fresh by fastforce

  show ?thesis using 1 2 by argo
qed

lemma Abs_lst_rename_deep:
  fixes a c::"'a::at" and x::"'b::fs" and e::"'c::fs" and e2::"'d::fs" and f::"'d * 'c * 'b \<Rightarrow> 'e::fs"
  assumes fresh: "atom c \<sharp> f (e2, e, x)" "atom c \<sharp> (e, x)" "atom a \<sharp> (e, x)"
  and eqvt_at: "eqvt_at f (e2, e, x)"
shows "[[atom a]]lst. f (e2, e, x) = [[atom c]]lst. f ((a \<leftrightarrow> c) \<bullet> e2, e, x)"
proof -
  have 1: "[[atom a]]lst. f (e2, e, x) = [[atom c]]lst. (a \<leftrightarrow> c) \<bullet> f (e2, e, x)" by (rule Abs_lst_rename[OF fresh(1)])
  have 2: "(a \<leftrightarrow> c) \<bullet> f (e2, e, x) = f ((a \<leftrightarrow> c) \<bullet> e2, e, x)" by (rule eqvt_at_deep[OF fresh(3) fresh(2) eqvt_at])
  show ?thesis using 1 2 by argo
qed

lemma Abs_lst_rename_both:
  fixes a c::"'a::at" and e e'::"'b::fs"
  assumes fresh: "atom c \<sharp> (y, e, y', e')"
  and equal: "[[atom y]]lst. e = [[atom y']]lst. e'"
shows "(y \<leftrightarrow> c) \<bullet> e = (y' \<leftrightarrow> c) \<bullet> e'"
proof -
  from assms have "(y \<leftrightarrow> c) \<bullet> ([[atom y]]lst. e) = (y' \<leftrightarrow> c) \<bullet> ([[atom y']]lst. e')" by auto
  then have "[[atom c]]lst. (y \<leftrightarrow> c) \<bullet> e = [[atom c]]lst. (y' \<leftrightarrow> c) \<bullet> e'" by auto
  then show ?thesis using Abs1_eq(3) by blast
qed

lemma Abs_sumC:
  fixes y y'::"'a::at" and x x'::"'b::fs" and e e'::"'c::fs" and e2 e2'::"'d::fs" and f::"'d * 'c * 'b \<Rightarrow> 'e::fs"
  assumes fresh: "atom y \<sharp> (e, x)" "atom y' \<sharp> (e', x')"
  and eqvt_at: "eqvt_at f (e2, e, x)" "eqvt_at f (e2', e', x')"
  and equal: "[[atom y]]lst. e2 = [[atom y']]lst. e2'" "x = x'" "e = e'"
  shows "[[atom y]]lst. f (e2, e, x) = [[atom y']]lst. f (e2', e', x')"
proof -
  obtain c::"'a" where "atom c \<sharp> (y, y', e, e', x, x', e2, e2', f (e2, e, x), f (e2', e', x'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> f (e2, e, x)" "atom c \<sharp> (e, x)" "atom c \<sharp> f (e2', e', x')"  "atom c \<sharp> (e', x')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by auto

  have 1: "[[atom y]]lst. f (e2, e, x) = [[atom c]]lst. f ((y \<leftrightarrow> c) \<bullet> e2, e, x)" by (rule Abs_lst_rename_deep[OF c(1) c(2) fresh(1) eqvt_at(1)])
  have 2: "[[atom y']]lst. f (e2', e', x') = [[atom c]]lst. f ((y' \<leftrightarrow> c) \<bullet> e2', e', x')" by (rule Abs_lst_rename_deep[OF c(3) c(4) fresh(2) eqvt_at(2)])
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" by (rule Abs_lst_rename_both[OF c(5) equal(1)])

  show ?thesis using 1 2 3 equal by argo
qed

lemma Abs_sumC_star:
  fixes ys ys'::"atom list" and x x'::"'a::fs" and e e'::"'b::fs" and e2 e2'::"'c::fs" and f::"'c * 'b * 'a \<Rightarrow> 'd::fs"
  assumes fresh: "set ys \<sharp>* (e, x)" "set ys' \<sharp>* (e', x')"
  and eqvt_at: "eqvt_at f (e2, e, x)" "eqvt_at f (e2', e', x')"
  and equal: "[ys]lst. e2 = [ys']lst. e2'" "x = x'" "e = e'"
  shows "[ys]lst. f (e2, e, x) = [ys']lst. f (e2', e', x')"
proof -
  have 1: "set ys \<sharp>* ([ys]lst. f (e2, e, x))" by (simp add: Abs_fresh_star(3))
  have 2: "\<And>p. supp p \<sharp>* (e, x) \<Longrightarrow> p \<bullet> ([ys]lst. f (e2, e, x)) = [p \<bullet> ys]lst. f (p \<bullet> e2, e, x)" using eqvt_at(1) by (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  have 3: "\<And>p. supp p \<sharp>* (e, x) \<Longrightarrow> p \<bullet> ([ys']lst. f (e2', e, x)) = [p \<bullet> ys']lst. f (p \<bullet> e2', e, x)" using eqvt_at(2) equal(2,3) by (simp add: eqvt_at_def, simp add: fresh_star_Pair perm_supp_eq)
  show ?thesis using Abs_lst_fcb2[where f="\<lambda>a b c. [a]lst. f (b, e, x)", OF equal(1) 1 fresh(1) _ 2 3] fresh(2) equal(2,3) by simp
qed

lemma Abs_fresh_var:
  fixes y::"'a::at" and e ::"'b::fs"
  obtains c::"'a" and e'::"'b" where "([[atom y]]lst. e = [[atom c]]lst. e') \<and> atom y \<sharp> [[atom c]]lst. e'"
proof -
  obtain c::"'a" where "atom c \<sharp> (y, e)" using obtain_fresh by blast
  have 1: "[[atom y]]lst. e = [[atom c]]lst. (y \<leftrightarrow> c) \<bullet> e" using Abs_lst_rename \<open>atom c \<sharp> (y, e)\<close> by fastforce
  have 2: "atom y \<sharp> [[atom c]]lst. (y \<leftrightarrow> c) \<bullet> e"
    by (metis Abs_fresh_iff(3) \<open>atom c \<sharp> (y, e)\<close> flip_at_simps(2) fresh_PairD(2) fresh_at_base_permute_iff)
  from 1 2 show ?thesis using that[of c "(y \<leftrightarrow> c) \<bullet> e"] by simp
qed

lemma Abs_rename_body:
  fixes a b::"'a::at" and e1 e2::"'b::fs"
  assumes  "[[atom a]]lst. e1 = [[atom b]]lst. e2"
  shows "(a \<leftrightarrow> b) \<bullet> e1 = e2"
  by (metis Abs1_eq_iff'(3) Nominal2_Base.swap_self assms flip_commute flip_def fresh_star_zero supp_perm_eq_test)


lemma fresh_filter: "a = b \<or> atom a \<sharp> xs \<Longrightarrow> atom a \<sharp> filter (\<lambda>x. x \<noteq> b) xs"
  by (induction xs) (auto simp: fresh_Cons fresh_Nil)

lemma Projl_permute: "\<exists>y. f = Inl y \<Longrightarrow> p \<bullet> projl f = projl (p \<bullet> f)" by auto
lemma Projr_permute: "\<exists>y. f = Inr y \<Longrightarrow> p \<bullet> projr f = projr (p \<bullet> f)" by auto

lemma eqvt_fBall[eqvt]: "p \<bullet> fBall s f = fBall (p \<bullet> s) (p \<bullet> f)"
  apply auto
  apply (metis eqvt_bound eqvt_lambda fBallE in_fset_eqvt permute_pure)
  by (metis eqvt_apply fBallE fBallI in_fset_eqvt permute_pure)

end
