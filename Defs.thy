theory Defs
  imports Syntax Nominal2_Lemmas "HOL-Library.Adhoc_Overloading"
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

nominal_function head_ctor :: "term \<Rightarrow> bool" where
  "head_ctor (Var _) = False"
| "head_ctor (Lam _ _ _) = False"
| "head_ctor (TyLam _ _ _) = False"
| "head_ctor (App e1 e2) = head_ctor e1"
| "head_ctor (TApp e _) = head_ctor e"
| "head_ctor (Ctor _) = True"
| "head_ctor (Let _ _ _ _) = False"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: term.exhaust)
qed (auto simp: eqvt_def head_ctor_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function is_value :: "term => bool" where
  "is_value (Var x) = False"
| "is_value (\<lambda> x : \<tau> . e) = True"
| "is_value (\<Lambda> a : k . e) = is_value e"
| "is_value (App e1 e2) = head_ctor e1"
| "is_value (TApp e \<tau>) = head_ctor e"
| "is_value (Ctor _) = True"
| "is_value (Let x \<tau> e1 e2) = False"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: term.exhaust)
next
  case (17 a k e a' k' e')
  obtain c::tyvar where c: "atom c \<sharp> (a, e, a', e')" by (rule obtain_fresh)
  have 1: "is_value_sumC e' = (a' \<leftrightarrow> c) \<bullet> is_value_sumC e'" using permute_boolE permute_boolI by blast
  have 2: "is_value_sumC e = (a \<leftrightarrow> c) \<bullet> is_value_sumC e" using permute_boolE permute_boolI by blast
  from c have "(a \<leftrightarrow> c) \<bullet> e = (a' \<leftrightarrow> c) \<bullet> e'" using 17(5) by simp
  then show ?case using 1 2 17(1,2) eqvt_at_def by metis
qed (auto simp: eqvt_def is_value_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_term :: "term => term \<Rightarrow> var => term" where
  "subst_term (Var y) e x  = (if x = y then e else Var y)"
| "subst_term (App e1 e2) e x = App (subst_term e1 e x) (subst_term e2 e x)"
| "subst_term (TApp e1 \<tau>) e x = TApp (subst_term e1 e x) \<tau>"
| "subst_term (Ctor D) _ _ = Ctor D"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<lambda> y:\<tau>. e2) e x = (\<lambda> y:\<tau>. subst_term e2 e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<Lambda> y:k. e2) e x = (\<Lambda> y:k. subst_term e2 e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (Let y \<tau> e1 e2) e x = Let y \<tau> (subst_term e1 e x) (subst_term e2 e x)"
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

nominal_function subst_type :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> \<tau>" where
  "subst_type (TyData T) _ _ = TyData T"
| "subst_type (TyVar b) \<tau> a = (if a=b then \<tau> else TyVar b)"
| "subst_type TyArrow _ _ = TyArrow"
| "subst_type (TyApp \<tau>1 \<tau>2) \<tau> a = TyApp (subst_type \<tau>1 \<tau> a) (subst_type \<tau>2 \<tau> a)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_type (\<forall> b:k. \<sigma>) \<tau> a = (\<forall>b:k. subst_type \<sigma> \<tau> a)"
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

nominal_function subst_term_type :: "term \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> term" where
  "subst_term_type (Var x) _ _ = Var x"
| "subst_term_type (Ctor D) _ _ = Ctor D"
| "subst_term_type (App e1 e2) \<tau> a = App (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"
| "subst_term_type (TApp e \<tau>2) \<tau> a = TApp (subst_term_type e \<tau> a) (subst_type \<tau>2 \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<lambda> y:\<tau>'. e2) \<tau> a = (\<lambda> y:(subst_type \<tau>' \<tau> a). subst_term_type e2 \<tau> a)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<Lambda> b:k. e2) \<tau> a = (\<Lambda> b:k. subst_term_type e2 \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (Let y \<tau>' e1 e2) \<tau> a = Let y (subst_type \<tau>' \<tau> a) (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"
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

nominal_function subst_context :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> \<Gamma>" where
  "subst_context [] _ _ = []"
| "subst_context (BVar x \<tau> # \<Gamma>) \<tau>' a = BVar x (subst_type \<tau> \<tau>' a) # subst_context \<Gamma> \<tau>' a"
| "subst_context (BTyVar b k # \<Gamma>) \<tau>' a = (if a = b then subst_context \<Gamma> \<tau>' a else  BTyVar b k # subst_context \<Gamma> \<tau>' a)"
proof goal_cases
  case (3 P x)
  then obtain xs \<tau>' a where P: "x = (xs, \<tau>', a)" by (metis prod.exhaust)
  then show ?case using 3
  proof (cases xs)
    case (Cons a list)
    then show ?thesis using 3 P by (cases a rule: binder.exhaust) auto
  qed auto
qed (auto simp: eqvt_def subst_context_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

no_notation inverse_divide (infixl "'/" 70)
consts subst :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" ("_[_'/_]" [1000,0,0] 1000)

adhoc_overloading
  subst subst_term subst_type subst_term_type subst_context

end
