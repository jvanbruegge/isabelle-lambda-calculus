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

nominal_function is_value :: "term => bool" where
  "is_value (Var x) = False"
| "is_value (\<lambda> x : \<tau> . e) = True"
| "is_value (\<Lambda> a : k . e) = True"
| "is_value (Ctor _ _ _) = True"
| "is_value (Let x \<tau> e1 e2) = False"
| "is_value (App e1 e2) = False"
| "is_value (TApp e \<tau>) = False"
  apply (auto simp: eqvt_def is_value_graph_aux_def)
  using term_elist.exhaust by blast
nominal_termination (eqvt) by lexicographic_order

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)")
      subst_term :: "term => term \<Rightarrow> var => term"
  and subst_term_list :: "elist \<Rightarrow> term \<Rightarrow> var \<Rightarrow> elist" where
  "subst_term (Var y) e x = (if x = y then e else Var y)"
| "subst_term (App e1 e2) e x = App (subst_term e1 e x) (subst_term e2 e x)"
| "subst_term (TApp e1 \<tau>) e x = TApp (subst_term e1 e x) \<tau>"
| "subst_term (Ctor D tys terms) e x = Ctor D tys (subst_term_list terms e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<lambda> y:\<tau>. e2) e x = (\<lambda> y:\<tau>. subst_term e2 e x)" 
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<Lambda> y:k. e2) e x = (\<Lambda> y:k. subst_term e2 e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (Let y \<tau> e1 e2) e x = Let y \<tau> (subst_term e1 e x) (subst_term e2 e x)"

| "subst_term_list ENil _ _ = ENil"
| "subst_term_list (ECons y ys) e x = ECons (subst_term y e x) (subst_term_list ys e x)"
proof goal_cases
  (* this is adapted and simplified from here: https://www.joachim-breitner.de/thesis/isa/Substitution.thy *)
  have eqvt_at_subst_term: "\<And>e y z . eqvt_at subst_term_subst_term_list_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_term a b c) (e, y, z)"
    apply (simp add: eqvt_at_def subst_term_def)
    apply rule
    apply (subst Projl_permute)
     apply (simp add: subst_term_subst_term_list_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_term_subst_term_list_graph (Inl (e, y, z)))")
      apply(simp)
      apply(auto)[1]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_term_subst_term_list_graph.cases)
               apply(assumption)
              apply blast+
    apply simp
    done
{
  case (3 P x)
  then show ?case
  proof (cases x)
    case (Inl a)
    then obtain t e y where P: "a = (t, e, y)" by (metis prod.exhaust)
    then show ?thesis using Inl 3
      apply (cases t rule: term_elist.strong_exhaust(1)[of _ _ "(e, y)"])
      apply blast+
      using fresh_star_insert by fastforce+
  next
    case (Inr b)
    then obtain ys e y where P: "b = (ys, e, y)" by (metis prod.exhaust)
    then show ?thesis using 3 Inr by (cases ys rule: term_elist.exhaust(2)) auto
  qed
next
  case (34 y e x \<tau> e2 y' e' x' \<tau>' e2')
  have "(\<lambda>y:\<tau>. subst_term e2 e x) = (\<lambda>y':\<tau>'. subst_term e2' e' x')" using Abs_sumC[OF 34(5,6) eqvt_at_subst_term[OF 34(1)] eqvt_at_subst_term[OF 34(2)]] 34(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (39 y e x k e2 y' e' x' k' e2')
  have "(\<Lambda> y:k. subst_term e2 e x) = (\<Lambda> y':k'. subst_term e2' e' x')" using Abs_sumC[OF 39(5,6) eqvt_at_subst_term[OF 39(1)] eqvt_at_subst_term[OF 39(2)]] 39(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (43 y e x \<tau> e1 e2 y' e' x' \<tau>' e1' e2')
  have "Let y \<tau> (subst_term e1 e x) (subst_term e2 e x) = Let y' \<tau>' (subst_term e1' e' x') (subst_term e2' e' x')" using Abs_sumC[OF 43(9,10) eqvt_at_subst_term[OF 43(2)] eqvt_at_subst_term[OF 43(4)]] 43(11) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
} qed (auto simp: eqvt_def subst_term_subst_term_list_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)")
  subst_type :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> \<tau>"
  and subst_type_list :: "tlist \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> tlist" where
  "subst_type (TyVar b) \<tau> a = (if a = b then \<tau> else TyVar b)"
| "subst_type (TyData T tys) \<tau> a = TyData T (subst_type_list tys \<tau> a)"
| "subst_type TyArrow _ _ = TyArrow"
| "subst_type (TyApp \<tau>1 \<tau>2) \<tau> a = TyApp (subst_type \<tau>1 \<tau> a) (subst_type \<tau>2 \<tau> a)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_type (\<forall> b:k. \<sigma>) \<tau> a = (\<forall> b:k. subst_type \<sigma> \<tau> a)"

| "subst_type_list TNil _ _ = TNil"
| "subst_type_list (TCons t tys) \<tau> a = TCons (subst_type t \<tau> a) (subst_type_list tys \<tau> a)"
proof goal_cases
  case (3 P x)
  then show ?case
  proof (cases x)
    case (Inl a)
    then obtain t \<tau> b where "a = (t, \<tau>, b)" by (metis prod.exhaust)
    then show ?thesis using 3 Inl
      apply (cases t rule: \<tau>_tlist.strong_exhaust(1)[of _ _ "(\<tau>, b)"])
          apply blast+
      using fresh_star_insert by fastforce
  next
    case (Inr b)
    then obtain tys \<tau> a where "b = (tys, \<tau>, a)" by (metis prod.exhaust)
    then show ?thesis using 3 Inr by (cases tys rule: \<tau>_tlist.strong_exhaust(2)) auto
  qed
next
  case (26 b \<tau> a k \<sigma> b' \<tau>' a' k' \<sigma>')
  (* this is adapted and simplified from here: https://www.joachim-breitner.de/thesis/isa/Substitution.thy *)
  have eqvt_at_subst_type: "\<And>e y z . eqvt_at subst_type_subst_type_list_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_type a b c) (e, y, z)"
    apply (simp add: eqvt_at_def subst_type_def)
    apply rule
    apply (subst Projl_permute)
     apply (simp add: subst_type_subst_type_list_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_type_subst_type_list_graph (Inl (e, y, z)))")
      apply(simp)
      apply(auto)[1]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_type_subst_type_list_graph.cases)
               apply(assumption)
              apply blast+
    apply simp
    done
  have "(\<forall> b:k. subst_type \<sigma> \<tau> a) = (\<forall> b':k'. subst_type \<sigma>' \<tau>' a')" using Abs_sumC[OF 26(5,6) eqvt_at_subst_type[OF 26(1)] eqvt_at_subst_type[OF 26(2)]] 26(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_type_def, symmetric, unfolded fun_eq_iff])
qed (auto simp: eqvt_def subst_type_subst_type_list_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined)")
  subst_term_type :: "term \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> term"
  and subst_term_list_type :: "elist \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> elist" where
  "subst_term_type (Var x) _ _ = Var x"
| "subst_term_type (Ctor D tys terms) \<tau> a = Ctor D (subst_type_list tys \<tau> a) (subst_term_list_type terms \<tau> a)"
| "subst_term_type (App e1 e2) \<tau> a = App (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"
| "subst_term_type (TApp e \<tau>2) \<tau> a = TApp (subst_term_type e \<tau> a) (subst_type \<tau>2 \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<lambda> y:\<tau>'. e2) \<tau> a = (\<lambda> y:(subst_type \<tau>' \<tau> a). subst_term_type e2 \<tau> a)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<Lambda> b:k. e2) \<tau> a = (\<Lambda> b:k. subst_term_type e2 \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (Let y \<tau>' e1 e2) \<tau> a = Let y (subst_type \<tau>' \<tau> a) (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"

| "subst_term_list_type ENil _ _ = ENil"
| "subst_term_list_type (ECons y ys) \<tau> a = ECons (subst_term_type y \<tau> a) (subst_term_list_type ys \<tau> a)"
proof goal_cases
(* this is adapted and simplified from here: https://www.joachim-breitner.de/thesis/isa/Substitution.thy *)
  have eqvt_at_subst_type_term: "\<And>e y z . eqvt_at subst_term_type_subst_term_list_type_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_term_type a b c) (e, y, z)"
    apply (simp add: eqvt_at_def subst_term_type_def)
    apply rule
    apply (subst Projl_permute)
     apply (simp add: subst_term_type_subst_term_list_type_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_term_type_subst_term_list_type_graph (Inl (e, y, z)))")
      apply(simp)
      apply(auto)[1]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_term_type_subst_term_list_type_graph.cases)
               apply(assumption)
              apply blast+
    apply simp
    done
{
  case (3 P x)
  then show ?case
  proof (cases x)
    case (Inl a)
    then obtain t \<tau> b where "a = (t, \<tau>, b)" by (metis prod.exhaust)
    then show ?thesis using Inl 3
      apply (cases t rule: term_elist.strong_exhaust(1)[of _ _ "(\<tau>, b)"])
            apply blast+
      using fresh_star_insert by fastforce+
  next
    case (Inr b)
    then obtain xs \<tau> a where "b = (xs, \<tau>, a)" by (metis prod.exhaust)
    then show ?thesis using Inr 3 by (cases xs rule: term_elist.strong_exhaust(2)) auto
  qed
next
  case (34 y \<tau> a \<tau>2 e2 y' \<tau>' a' \<tau>2' e2')
  have "(\<lambda>y:(subst_type \<tau>2 \<tau> a). subst_term_type e2 \<tau> a) = (\<lambda>y':(subst_type \<tau>2' \<tau>' a'). subst_term_type e2' \<tau>' a')"
    using Abs_sumC[OF 34(5,6) eqvt_at_subst_type_term[OF 34(1)] eqvt_at_subst_type_term[OF 34(2)]] 34(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (39 b \<tau> a k e2 b' \<tau>' a' k' e2')
  have "(\<Lambda> b:k. subst_term_type e2 \<tau> a) = (\<Lambda> b':k'. subst_term_type e2' \<tau>' a')" using Abs_sumC[OF 39(5,6) eqvt_at_subst_type_term[OF 39(1)] eqvt_at_subst_type_term[OF 39(2)]] 39(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (43 y \<tau> a \<tau>2 e1 e2 y' \<tau>' a' \<tau>2' e1' e2')
  have "Let y (subst_type \<tau>2 \<tau> a) (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a) = Let y' (subst_type \<tau>2' \<tau>' a') (subst_term_type e1' \<tau>' a') (subst_term_type e2' \<tau>' a')"
    using Abs_sumC[OF 43(9,10) eqvt_at_subst_type_term[OF 43(2)] eqvt_at_subst_type_term[OF 43(4)]] 43(11) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
} qed (auto simp: eqvt_def subst_term_type_subst_term_list_type_graph_aux_def)
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
  subst subst_term subst_term_list subst_type subst_type_list subst_term_type subst_term_list_type subst_context

end
