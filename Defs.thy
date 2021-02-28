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

nominal_function ctor_data_app :: "\<tau> \<Rightarrow> (data_name * tyvar list) option" where
  "ctor_data_app (TyVar _) = None"
| "ctor_data_app (TyData T) = Some (T, [])"
| "ctor_data_app TyArrow = None"
| "ctor_data_app (TyApp \<tau>1 (TyVar a)) = (case ctor_data_app \<tau>1 of
    Some (T, s) \<Rightarrow> Some (T, a#s)
  | None \<Rightarrow> None)"
| "ctor_data_app (TyApp _ (TyData _)) = None"
| "ctor_data_app (TyApp _ TyArrow) = None"
| "ctor_data_app (TyApp _ (TyApp _ _)) = None"
| "ctor_data_app (TyApp _ (TyForall _ _ _)) = None"
| "ctor_data_app (TyForall _ _ _) = None"
proof goal_cases
  case 1
  then show ?case by (auto simp: eqvt_def ctor_data_app_graph_aux_def split!: option.splits)
next
  case (3 P x)
  then show ?case
  proof (cases x rule: \<tau>.exhaust)
    case (TyApp \<tau>1 \<tau>2)
    then show ?thesis using 3 by (cases \<tau>2 rule: \<tau>.exhaust) auto
  qed (auto simp: 3)
qed auto
nominal_termination (eqvt) by lexicographic_order

nominal_function ctor_type_app :: "\<tau> \<Rightarrow> (data_name * tyvar list) option" where
  "ctor_type_app (TyVar _) = None"
| "ctor_type_app (TyData T) = Some (T, [])"
| "ctor_type_app TyArrow = None"
| "ctor_type_app (TyApp (TyApp TyArrow \<tau>1) \<tau>2) = ctor_type_app \<tau>2"
| "ctor_type_app (TyApp (TyApp (TyVar a) \<tau>1) \<tau>2) = ctor_data_app (TyApp (TyApp (TyVar a) \<tau>1) \<tau>2)"
| "ctor_type_app (TyApp (TyApp (TyData T) \<tau>1) \<tau>2) = ctor_data_app (TyApp (TyApp (TyData T) \<tau>1) \<tau>2)"
| "ctor_type_app (TyApp (TyApp (TyApp \<tau>1' \<tau>2') \<tau>1) \<tau>2) = ctor_data_app (TyApp (TyApp (TyApp \<tau>1' \<tau>2') \<tau>1) \<tau>2)"
| "ctor_type_app (TyApp (TyApp (TyForall a k e) \<tau>1) \<tau>2) = ctor_data_app (TyApp (TyApp (TyForall a k e) \<tau>1) \<tau>2)"
| "ctor_type_app (TyApp (TyVar a) \<tau>2) = ctor_data_app (TyApp (TyVar a) \<tau>2)"
| "ctor_type_app (TyApp (TyData T) \<tau>2) = ctor_data_app (TyApp (TyData T) \<tau>2)"
| "ctor_type_app (TyApp TyArrow \<tau>2) = ctor_data_app (TyApp TyArrow \<tau>2)"
| "ctor_type_app (TyApp (TyForall a k e) \<tau>2) = ctor_data_app (TyApp (TyForall a k e) \<tau>2)"
| "ctor_type_app (TyForall _ _ _) = None"
proof goal_cases
  case (3 P x)
  show ?case using 3(1-3,13)
  proof (cases x rule: \<tau>.exhaust)
    case outer: (TyApp \<tau>1 \<tau>2)
    then show ?thesis using 3(9-12)
    proof (cases \<tau>1 rule: \<tau>.exhaust)
      case inner: (TyApp \<tau>1' \<tau>2')
      then show ?thesis using outer 3(4-8) by (cases \<tau>1' rule: \<tau>.exhaust) blast+
    qed blast+
  qed blast+
next
  case (74 a k e \<tau>1 \<tau>2 a k e \<tau>1 \<tau>2)
  then show ?case by (simp add: 74)
next
  case (92 a k e \<tau>2 a k e \<tau>2)
  then show ?case by (simp add: 92)
qed (auto simp: eqvt_def ctor_type_app_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function ctor_type_forall :: "\<tau> \<Rightarrow> (data_name * tyvar list) option" where
  "ctor_type_forall (TyVar _) = None"
| "ctor_type_forall (TyData T) = Some (T, [])"
| "ctor_type_forall TyArrow = None"
| "ctor_type_forall (TyApp \<tau>1 \<tau>2) = ctor_type_app (TyApp \<tau>1 \<tau>2)"
| "ctor_type_forall (TyForall a _ e) = (case ctor_type_forall e of
    Some (T, s) \<Rightarrow> (if a \<in> set s then Some (T, filter (\<lambda>x. x \<noteq> a) s) else None)
  | None \<Rightarrow> None)"
proof goal_cases
  case 1
  then show ?case by (auto simp: eqvt_def ctor_type_forall_graph_aux_def split!: option.splits list.splits)
next
  case (3 P x)
  then show ?case by (cases x rule: \<tau>.exhaust)
next
  case (18 a k e a' k' e')
  obtain c::tyvar where P: "atom c \<sharp> (a, e, a', e', ctor_type_forall_sumC e, ctor_type_forall_sumC e')" by (rule obtain_fresh)
  then have c: "atom c \<sharp> a" "atom c \<sharp> e" "atom c \<sharp> a'" "atom c \<sharp> e'" "atom c \<sharp> ctor_type_forall_sumC e" "atom c \<sharp> ctor_type_forall_sumC e'" by auto
  have 1: "(a \<leftrightarrow> c) \<bullet> e = (a' \<leftrightarrow> c) \<bullet> e'" using Abs_lst_rename_both c(1-4) 18(5) by auto
  then have 2: "(a \<leftrightarrow> c) \<bullet> ctor_type_forall_sumC e = (a' \<leftrightarrow> c) \<bullet> ctor_type_forall_sumC e'" using 18(1,2) eqvt_at_def by metis
  then have 3: "ctor_type_forall_sumC e = None \<longleftrightarrow> ctor_type_forall_sumC e' = None" using permute_eq_iff by fastforce
  then show ?case
  proof (cases "ctor_type_forall_sumC e")
    case (Some t)
    then obtain T s where P1: "t = (T, s)" by fastforce
    from Some obtain T' s' where P2: "ctor_type_forall_sumC e' = Some (T', s')" using 3 by auto
    have "T = T'" using "2" P1 P2 Some Some_eqvt option.inject perm_data_name_tyvar by auto
    have same: "(a \<leftrightarrow> c) \<bullet> s = (a' \<leftrightarrow> c) \<bullet> s'" using "2" P1 P2 Some by auto
    have x: "a \<in> set s \<longleftrightarrow> a' \<in> set s'" by (metis flip_at_simps(2) mem_permute_iff permute_flip_cancel same set_eqvt)
    have 4: "atom c \<sharp> s" using c(5) Some P1 fresh_Some fresh_Pair by metis
    have 5: "atom c \<sharp> s'" using c(6) Some P2 fresh_Some fresh_Pair by metis
    have 6: "atom a \<sharp> filter (\<lambda>x. x \<noteq> a) s" "atom a' \<sharp> filter (\<lambda>x. x \<noteq> a') s'" "atom c \<sharp> filter (\<lambda>x. x \<noteq> a) s" "atom c \<sharp> filter (\<lambda>x. x \<noteq> a') s'" using 4 5 fresh_filter by auto
    have 8: "filter (\<lambda>x. x \<noteq> a) s = (a \<leftrightarrow> c) \<bullet> filter (\<lambda>x. x \<noteq> a) s" using 6 flip_fresh_fresh by metis
    also have "... = filter (\<lambda>x. x \<noteq> c) ((a \<leftrightarrow> c) \<bullet> s)" by auto
    also have "... = filter (\<lambda>x. x \<noteq> c) ((a' \<leftrightarrow> c) \<bullet> s')" using same by argo
    also have "... = (a' \<leftrightarrow> c) \<bullet> filter (\<lambda>x. x \<noteq> a') s'" by simp
    also have "... = filter (\<lambda>x. x \<noteq> a') s'" using 6 flip_fresh_fresh by blast
    finally have 9: "Some (T, filter (\<lambda>x. x \<noteq> a) s) = Some (T', filter (\<lambda>x. x \<noteq> a') s')" using \<open>T = T'\<close> by blast
    then show ?thesis using Some P1 P2 x by simp
  qed simp
qed auto
nominal_termination (eqvt) by lexicographic_order

(* This function checks if a type has the form \<forall>[a:k]. [\<tau>] \<rightarrow> T [a] *)
nominal_function ctor_type :: "\<tau> \<Rightarrow> data_name option" where
  "ctor_type (TyVar a) = None"
| "ctor_type (TyData T) = Some T"
| "ctor_type TyArrow = None"
| "ctor_type (TyApp \<tau>1 \<tau>2) = (case ctor_type_app (TyApp \<tau>1 \<tau>2) of Some (T, []) \<Rightarrow> Some T | _ \<Rightarrow> None)"
| "ctor_type (TyForall a k e) = (case ctor_type_forall (TyForall a k e) of Some (T, []) \<Rightarrow> Some T | _ \<Rightarrow> None)"
proof goal_cases
  case 1
  then show ?case by (auto simp: eqvt_def ctor_type_graph_aux_def split!: option.splits list.splits)
next
  case (3 P x)
  then show ?case by (cases x rule: \<tau>.exhaust)
next
  case (18 a k e a' k' e')
  then show ?case by (simp add: 18)
qed auto
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
