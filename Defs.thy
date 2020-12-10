theory Defs
  imports Syntax Nominal2_Lemmas
begin

nominal_function isin :: "binder \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
  "isin _ [] = False"
| "isin (BVar x t) (BVar y t'#xs) = (if x = y then t = t' else isin (BVar x t) xs)"
| "isin (BVar x t) (BTyVar _ _#xs) = isin (BVar x t) xs"
| "isin (BTyVar a k) (BVar _ _#xs) = isin (BTyVar a k) xs"
| "isin (BTyVar a k1) (BTyVar b k2#xs) = (if a = b then k1 = k2 else isin (BTyVar a k1) xs)"
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
| "is_value (\<Lambda> a : k . e) = True"
| "is_value (App e1 e2) = False"
| "is_value (TyApp e \<tau>) = False"
| "is_value Unit = True"
| "is_value (Let x \<tau> e1 e2) = False"
  apply (auto simp: eqvt_def is_value_graph_aux_def)
  using term.exhaust by blast
nominal_termination (eqvt) by lexicographic_order

(** substitutions *)
nominal_function subst_term :: "term => term \<Rightarrow> var => term" ("_[_'/_]" [1000,0,0] 1000) where
  "(Var y)[e/x]  = (if x = y then e else Var y)"
| "(App e1 e2)[e/x] = App e1[e/x] e2[e/x]"
| "(TyApp e1 \<tau>)[e/x] = TyApp e1[e/x] \<tau>"
| "Unit[_/_] = Unit"
| "atom y \<sharp> (e, x) \<Longrightarrow> (\<lambda> y:\<tau>. e2)[e/x] = (\<lambda> y:\<tau>. e2[e/x])"
| "atom y \<sharp> (e, x) \<Longrightarrow> (\<Lambda> y:k. e2)[e/x] = (\<Lambda> y:k. e2[e/x])"
| "atom y \<sharp> (e, x) \<Longrightarrow> (Let y \<tau> e1 e2)[e/x] = (Let y \<tau> e1[e/x] e2[e/x])"
proof (goal_cases)
  case (3 P x)
  then obtain t e y where P: "x = (t, e, y)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(e, y)"])
          apply (auto simp: 3)
    using 3(5-7) P fresh_star_def by blast+
next
  case (26 y e x \<tau> e2 y' e' x' \<tau>' e2')
  then show ?case using Abs_sumC[OF 26(5,6,1,2)] by fastforce
next
  case (29 y e x k e2 y' e' x' k' e2')
  then show ?case using Abs_sumC[OF 29(5,6,1,2)] by fastforce
next
  case (31 y e x \<tau> e1 e2 y' e' x' \<tau>' e1' e2')
  then show ?case using Abs_sumC[OF 31(9,10,2,4)] by fastforce
qed (auto simp: eqvt_def subst_term_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_type :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> \<tau>" ("_[_'/_]" [1000,0,0] 1000) where
  "TyUnit[_/_] = TyUnit"
| "(TyVar b)[\<tau>/a] = (if a=b then \<tau> else TyVar b)"
| "(\<tau>1 \<rightarrow> \<tau>2)[\<tau>/a] = (\<tau>1[\<tau>/a] \<rightarrow> \<tau>2[\<tau>/a])"
| "(TyConApp \<tau>1 \<tau>2)[\<tau>/a] = TyConApp \<tau>1[\<tau>/a] \<tau>2[\<tau>/a]"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> (\<forall> b:k. \<sigma>)[\<tau>/a] = (\<forall>b:k. \<sigma>[\<tau>/a])"
proof goal_cases
  case (3 P x)
  then obtain t \<tau> a where P: "x = (t, \<tau>, a)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: \<tau>.strong_exhaust[of _ _ "(\<tau>, a)"])
       apply (auto simp: 3)
    using 3(5) P fresh_star_def by blast
next
  case (18 b \<tau> a k \<sigma> b' \<tau>' a' k' \<sigma>')
  then show ?case using Abs_sumC[OF 18(5,6,1,2)] by fastforce
qed (auto simp: eqvt_def subst_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_term_type :: "term \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> term" ("_[_'/_]" [1000,0,0] 1000) where
  "subst_term_type (Var x) _ _ = Var x"
| "subst_term_type Unit _ _ = Unit"
| "subst_term_type (App e1 e2) \<tau> a = App e1[\<tau>/a] e2[\<tau>/a]"
| "subst_term_type (TyApp e \<tau>2) \<tau> a = TyApp e[\<tau>/a] \<tau>2[\<tau>/a]"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<lambda> y:\<tau>'. e2) \<tau> a = (\<lambda> y:\<tau>'[\<tau>/a]. e2[\<tau>/a])"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<Lambda> b:k. e2) \<tau> a = (\<Lambda> b:k. e2[\<tau>/a])"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (Let y \<tau>' e1 e2) \<tau> a = Let y \<tau>'[\<tau>/a] e1[\<tau>/a] e2[\<tau>/a]"
proof goal_cases
  case (3 P x)
  then obtain t \<tau> a where P: "x = (t, \<tau>, a)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(\<tau>, a)"])
    using 3 P apply auto[4]
    using 3(5,6,7) P fresh_star_def by blast+
next
  case (26 y \<tau> a \<tau>1 e2 y' \<tau>' a' \<tau>1' e2')
  then show ?case using Abs_sumC[OF 26(5,6,1,2)] by fastforce
next
  case (29 b \<tau> a k e2 b' \<tau>' a' k' e2')
  then show ?case using Abs_sumC[OF 29(5,6,1,2)] by fastforce
next
  case (31 y \<tau> a \<tau>1 e1 e2 y' \<tau>' a' \<tau>1' e1' e2')
  then show ?case using Abs_sumC[OF 31(9,10,2,4)] by fastforce
qed (auto simp: eqvt_def subst_term_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

end
