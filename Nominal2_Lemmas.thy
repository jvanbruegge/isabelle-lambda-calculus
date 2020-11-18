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
  assumes fresh: "atom a \<sharp> (x, e)" "atom c \<sharp> (x, e)"
  and eqvt_at: "eqvt_at f (x, e, e2)"
shows "(a \<leftrightarrow> c) \<bullet> f (x, e, e2) = f (x, e, (a \<leftrightarrow> c) \<bullet> e2)"
proof -
  have 1: "(a \<leftrightarrow> c) \<bullet> f (x, e, e2) = f ((a \<leftrightarrow> c) \<bullet> (x, e, e2))" using eqvt_at eqvt_at_def by blast
  have 2: "(a \<leftrightarrow> c) \<bullet> (x, e, e2) = (x, e, (a \<leftrightarrow> c) \<bullet> e2)" using fresh fresh_Pair flip_fresh_fresh by fastforce

  show ?thesis using 1 2 by argo
qed

lemma Abs_lst_rename_deep:
  fixes a c::"'a::at" and x::"'b::fs" and e::"'c::fs" and e2::"'d::fs" and f::"'b * 'c * 'd \<Rightarrow> 'e::fs"
  assumes fresh: "atom c \<sharp> f (x, e, e2)" "atom c \<sharp> (x, e)" "atom a \<sharp> (x, e)"
  and eqvt_at: "eqvt_at f (x, e, e2)"
shows "[[atom a]]lst. f (x, e, e2) = [[atom c]]lst. f (x, e, (a \<leftrightarrow> c) \<bullet> e2)"
proof -
  have 1: "[[atom a]]lst. f (x, e, e2) = [[atom c]]lst. (a \<leftrightarrow> c) \<bullet> f (x, e, e2)" by (rule Abs_lst_rename[OF fresh(1)])
  have 2: "(a \<leftrightarrow> c) \<bullet> f (x, e, e2) = f (x, e, (a \<leftrightarrow> c) \<bullet> e2)" by (rule eqvt_at_deep[OF fresh(3) fresh(2) eqvt_at])
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
  fixes y y'::"'a::at" and x x'::"'b::fs" and e e'::"'c::fs" and e2 e2'::"'d::fs" and f::"'b * 'c * 'd \<Rightarrow> 'e::fs"
  assumes fresh: "atom y \<sharp> (x, e)" "atom y' \<sharp> (x', e')"
  and eqvt_at: "eqvt_at f (x, e, e2)" "eqvt_at f (x', e', e2')"
  and equal: "[[atom y]]lst. e2 = [[atom y']]lst. e2'" "x = x'" "e = e'"
  shows "[[atom y]]lst. f (x, e, e2) = [[atom y']]lst. f (x', e', e2')"
proof -
  obtain c::"'a" where "atom c \<sharp> (y, y', e, e', x, x', e2, e2', f (x, e, e2), f (x', e', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> f (x, e, e2)" "atom c \<sharp> (x, e)" "atom c \<sharp> f (x', e', e2')"  "atom c \<sharp> (x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by auto

  have 1: "[[atom y]]lst. f (x, e, e2) = [[atom c]]lst. f (x, e, (y \<leftrightarrow> c) \<bullet> e2)" by (rule Abs_lst_rename_deep[OF c(1) c(2) fresh(1) eqvt_at(1)])
  have 2: "[[atom y']]lst. f (x', e', e2') = [[atom c]]lst. f (x', e', (y' \<leftrightarrow> c) \<bullet> e2')" by (rule Abs_lst_rename_deep[OF c(3) c(4) fresh(2) eqvt_at(2)])
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" by (rule Abs_lst_rename_both[OF c(5) equal(1)])

  show ?thesis using 1 2 3 equal by argo
qed

end
