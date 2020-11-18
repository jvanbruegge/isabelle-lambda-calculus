theory Defs
  imports Syntax Nominal2_Lemmas
begin

nominal_function isin :: "binder \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
  "isin _ [] = False"
| "isin (BVar x t) (BVar y t'#xs) = (if x = y then t = t' else isin (BVar x t) xs)"
| "isin (BVar x t) (BTyVar a#xs) = isin (BVar x t) xs"
| "isin (BTyVar a) (BVar x t#xs) = isin (BTyVar a) xs"
| "isin (BTyVar a) (BTyVar b#xs) = (if a = b then True else isin (BTyVar a) xs)"
proof goal_cases
  case (3 P x)
  then obtain t ys where P: "x = (t, ys)" by (metis prod.exhaust)
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis using 3 P by blast
  next
    case (Cons a list)
    then show ?thesis
      apply (cases t rule: binder.exhaust)
       apply (cases a rule: binder.exhaust)
      using Cons 3 P apply auto
      apply (cases a rule: binder.exhaust)
      using Cons 3 P by auto
  qed
qed (auto simp: eqvt_def isin_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function
is_value :: "term => bool"
where
"is_value (Var x) = False"
| "is_value (\<lambda> x : \<tau> . e) = True"
| "is_value (\<Lambda> a . e) = True"
| "is_value (App e1 e2) = False"
| "is_value (TyApp e \<tau>) = False"
| "is_value Unit = True"
| "is_value (Let x \<tau> e1 e2) = False"
  apply (auto simp: eqvt_def is_value_graph_aux_def)
  using term.exhaust by blast
nominal_termination (eqvt) by lexicographic_order

(** substitutions *)
nominal_function subst_term :: "term => var => term => term" where
  "subst_term e x (Var y) = (if x=y then e else Var y)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term e x (\<lambda> y : \<tau> . e2) = (Lam y \<tau> (subst_term e x e2))"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term e x (\<Lambda> y . e2) = (\<Lambda> y . subst_term e x e2)"
| "subst_term e x (App e1 e2) = (App (subst_term e x e1) (subst_term e x e2))"
| "subst_term e x (TyApp e1 \<tau>) = (TyApp (subst_term e x e1) \<tau>)"
| "subst_term _ _ Unit = Unit"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term e x (Let y \<tau> e1 e2) = (Let y \<tau> (subst_term e x e1) (subst_term e x e2))"
proof goal_cases
  case (3 P x)
  then obtain e y t where P: "x = (e, y, t)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(e, y)"])
         apply (auto simp: 3)
    using 3(2) 3(3) 3(7) P fresh_star_def by blast+
next
  case (11 y x e \<tau> e2 y' x' e' \<tau>' e2')
  then show ?case using Abs_sumC[OF 11(5) 11(6) 11(1) 11(2)] by fastforce
next
  case (17 y x e e2 y' x' e' e2')
  then show ?case using Abs_sumC[OF 17(5) 17(6) 17(1) 17(2)] by fastforce
next
  case (31 y x e \<tau> e1 e2 y' x' e' \<tau>' e1' e2')
  then show ?case using Abs_sumC[OF 31(9) 31(10) 31(2) 31(4)] by fastforce
qed (auto simp: eqvt_def subst_term_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_type :: "\<tau> \<Rightarrow> tyvar \<Rightarrow> \<tau> \<Rightarrow> \<tau>" where
  "subst_type _ _ TyUnit = TyUnit"
| "subst_type \<tau> a (TyVar b) = (if a=b then \<tau> else TyVar b)"
| "subst_type \<tau> a (TyArrow \<tau>1 \<tau>2) = TyArrow (subst_type \<tau> a \<tau>1) (subst_type \<tau> a \<tau>2)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_type \<tau> a (TyForall b \<sigma>) = TyForall b (subst_type \<tau> a \<sigma>)"
proof goal_cases
  case (3 P x)
  then obtain \<tau> a t where P: "x = (\<tau>, a, t)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: \<tau>.strong_exhaust[of _ _ "(\<tau>, a)"])
       apply (auto simp: 3)
    using 3(4) P fresh_star_def by blast
next
  case (13 b \<tau> a \<sigma> b' \<tau>' a' \<sigma>')
  then show ?case using Abs_sumC[OF 13(5) 13(6) 13(1) 13(2)] by fastforce
qed (auto simp: eqvt_def subst_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_term_type :: "\<tau> \<Rightarrow> tyvar \<Rightarrow> term \<Rightarrow> term" where
  "subst_term_type _ _ (Var x) = Var x"
| "subst_term_type _ _ Unit = Unit"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type \<tau> a (\<lambda> y : \<tau>' . e2) = (Lam y (subst_type \<tau> a \<tau>') (subst_term_type \<tau> a e2))"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type \<tau> a (\<Lambda> b . e2) = (TyLam b (subst_term_type \<tau> a e2))"
| "subst_term_type \<tau> a (App e1 e2) = App (subst_term_type \<tau> a e1) (subst_term_type \<tau> a e2)"
| "subst_term_type \<tau> a (TyApp e \<tau>2) = TyApp (subst_term_type \<tau> a e) (subst_type \<tau> a \<tau>2)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type \<tau> a (Let y \<tau>' e1 e2) = Let y (subst_type \<tau> a \<tau>') (subst_term_type \<tau> a e1) (subst_term_type \<tau> a e2)"
proof goal_cases
  case (3 P x)
  then obtain \<tau> a t where P: "x = (\<tau>, a, t)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(\<tau>, a)"])
    using 3 P apply auto[4]
    using 3(3) 3(4) 3(7) P fresh_star_def by blast+
next
  case (17 y \<tau> a \<tau>2 e y' \<tau>' a' \<tau>2' e')
  then show ?case using Abs_sumC[OF 17(5) 17(6) 17(1) 17(2)] by fastforce
next
  case (22 b \<tau> a e b' \<tau>' a' e')
  then show ?case using Abs_sumC[OF 22(5) 22(6) 22(1) 22(2)] by fastforce
next
  case (31 y a \<tau> \<tau>2 e1 e2 y' a' \<tau>' \<tau>2' e1' e2')
  then show ?case using Abs_sumC[OF 31(9) 31(10) 31(2) 31(4)] by fastforce
qed (auto simp: eqvt_def subst_term_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

end