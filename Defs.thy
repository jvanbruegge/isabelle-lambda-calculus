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
| "head_ctor (Case _ _) = False"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: term_alt_list_alt.exhaust(1))
qed (auto simp: eqvt_def head_ctor_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function head_data :: "\<tau> \<Rightarrow> data_name option" where
  "head_data (TyVar _) = None"
| "head_data (TyData T) = Some T"
| "head_data TyArrow = None"
| "head_data (TyApp (TyData T) _) = Some T"
| "head_data (TyApp (TyVar _) _) = None"
| "head_data (TyApp TyArrow _) = None"
| "head_data (TyApp (TyApp _ _) _) = None"
| "head_data (TyApp (TyForall _ _ _) _) = None"
| "head_data (TyForall _ _ _) = None"
proof goal_cases
  case (3 P x)
  then show ?case
  proof (cases x rule: \<tau>.exhaust)
    case (TyApp \<tau>1 \<tau>2)
    then show ?thesis using 3 by (cases \<tau>1 rule: \<tau>.exhaust) auto
  qed
qed (auto simp: eqvt_def head_data_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function set_alt_list :: "alt_list \<Rightarrow> alt set" where
  "set_alt_list ANil = {}"
| "set_alt_list (ACons alt alts) = insert alt (set_alt_list alts)"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: term_alt_list_alt.exhaust(2))
qed (auto simp: eqvt_def set_alt_list_graph_aux_def)
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

abbreviation exhaustive :: "alt_list \<Rightarrow> \<Delta> \<Rightarrow> data_name \<Rightarrow> bool" where
  "exhaustive alts \<Delta> T \<equiv>
    (\<nexists>x e. MatchVar x e \<in> set_alt_list alts) \<longrightarrow>
      (\<forall>D \<tau>.
          (AxCtor D \<tau> \<in> set \<Delta> \<and> ctor_type \<tau> = Some T) \<longrightarrow>
          (\<exists>tys vals e. MatchCtor D tys vals e \<in> set_alt_list alts)
      )"

nominal_function is_value :: "term => bool" where
  "is_value (Var x) = False"
| "is_value (\<lambda> x : \<tau> . e) = True"
| "is_value (\<Lambda> a : k . e) = is_value e"
| "is_value (App e1 e2) = head_ctor e1"
| "is_value (TApp e \<tau>) = head_ctor e"
| "is_value (Ctor _) = True"
| "is_value (Let x \<tau> e1 e2) = False"
| "is_value (Case _ _) = False"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: term_alt_list_alt.exhaust(1))
next
  case (19 a k e a' k' e')
  obtain c::tyvar where c: "atom c \<sharp> (a, e, a', e')" by (rule obtain_fresh)
  have 1: "is_value_sumC e' = (a' \<leftrightarrow> c) \<bullet> is_value_sumC e'" using permute_boolE permute_boolI by blast
  have 2: "is_value_sumC e = (a \<leftrightarrow> c) \<bullet> is_value_sumC e" using permute_boolE permute_boolI by blast
  from c have "(a \<leftrightarrow> c) \<bullet> e = (a' \<leftrightarrow> c) \<bullet> e'" using 19(5) by simp
  then show ?case using 1 2 19(1,2) eqvt_at_def by metis
qed (auto simp: eqvt_def is_value_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (case_sum (\<lambda>x. Inr (Inl undefined)) (\<lambda>x. Inr (Inr undefined)))")
  subst_term :: "term => term \<Rightarrow> var => term" and
  subst_alt_list :: "alt_list \<Rightarrow> term \<Rightarrow> var \<Rightarrow> alt_list" and
  subst_alt :: "alt \<Rightarrow> term \<Rightarrow> var \<Rightarrow> alt" where

  "subst_term (Var y) e x  = (if x = y then e else Var y)"
| "subst_term (App e1 e2) e x = App (subst_term e1 e x) (subst_term e2 e x)"
| "subst_term (TApp e1 \<tau>) e x = TApp (subst_term e1 e x) \<tau>"
| "subst_term (Ctor D) _ _ = Ctor D"
| "subst_term (Case t alts) e x = Case (subst_term t e x) (subst_alt_list alts e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<lambda> y:\<tau>. e2) e x = (\<lambda> y:\<tau>. subst_term e2 e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (\<Lambda> y:k. e2) e x = (\<Lambda> y:k. subst_term e2 e x)"
| "atom y \<sharp> (e, x) \<Longrightarrow> subst_term (Let y \<tau> e1 e2) e x = Let y \<tau> (subst_term e1 e x) (subst_term e2 e x)"

| "subst_alt_list ANil _ _ = ANil"
| "subst_alt_list (ACons alt alts) e x = ACons (subst_alt alt e x) (subst_alt_list alts e x)"

| "atom y \<sharp> (e, x) \<Longrightarrow> subst_alt (MatchVar y t) e x = MatchVar y (subst_term t e x)"
| "set (map atom tys @ map atom vals) \<sharp>* (e, x) \<Longrightarrow> subst_alt (MatchCtor D tys vals t) e x = MatchCtor D tys vals (subst_term t e x)"
proof (goal_cases)

  (* this is adapted and simplified from here: https://www.joachim-breitner.de/thesis/isa/Substitution.thy *)
  have eqvt_at_term: "\<And>e y z . eqvt_at subst_term_subst_alt_list_subst_alt_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_term a b c) (e, y, z)"
    apply (simp add: eqvt_at_def subst_term_def)
    apply rule
    apply (subst Projl_permute)
     apply (simp add: subst_term_subst_alt_list_subst_alt_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_term_subst_alt_list_subst_alt_graph (Inl (e, y, z)))")
      apply(auto)[2]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_term_subst_alt_list_subst_alt_graph.cases)
               apply(assumption)
              apply blast+
    apply simp
    done

{ case (3 P x)
  then show ?case
  proof (cases x)
    case (Inl a)
    then obtain t e y where P: "a = (t, e, y)" by (metis prod.exhaust)
    then show ?thesis using 3(1-5) Inl
    proof (cases t rule: term_alt_list_alt.strong_exhaust(1)[of _ _ "(e, y)"])
      case Lam
      then show ?thesis using 3(6) Inl P fresh_star_insert by blast
    next
      case TyLam
      then show ?thesis using 3(7) Inl P fresh_star_insert by blast
    next
      case Let
      then show ?thesis using 3(8) Inl P fresh_star_insert by blast
    qed auto
  next
    case outer: (Inr b)
    then show ?thesis
    proof (cases b)
      case (Inl a)
      then obtain xs e y where "a = (xs, e, y)" by (metis prod.exhaust)
      then show ?thesis using 3(9,10) Inl outer by (cases xs rule: term_alt_list_alt.exhaust(2)) auto
    next
      case (Inr c)
      then obtain m e y where "c = (m, e, y)" by (metis prod.exhaust)
      then show ?thesis using 3(11,12) Inr outer fresh_star_insert
        apply (cases m rule: term_alt_list_alt.strong_exhaust(3)[of "(e, y)"])
         apply auto
        by blast
    qed
  qed
next
  case (54 y e x \<tau> e2 y' e' x' \<tau>' e2')
  have "(\<lambda> y : \<tau> . subst_term e2 e x) = (\<lambda> y' : \<tau>' . subst_term e2' e' x')" using Abs_sumC[OF 54(5,6) eqvt_at_term[OF 54(1)] eqvt_at_term[OF 54(2)]] 54(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (61 y e x k e2 y' e' x' k' e2')
  have "(\<Lambda> y : k . subst_term e2 e x) = (\<Lambda> y' : k' . subst_term e2' e' x')" using Abs_sumC[OF 61(5,6) eqvt_at_term[OF 61(1)] eqvt_at_term[OF 61(2)]] 61(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (67 y e x \<tau> e1 e2 y' e' x' \<tau>' e1' e2')
  have "Let y \<tau> (subst_term e1 e x) (subst_term e2 e x) = Let y' \<tau>' (subst_term e1' e' x') (subst_term e2' e' x')" using Abs_sumC[OF 67(9,10) eqvt_at_term[OF 67(2)] eqvt_at_term[OF 67(4)]] 67(11) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (79 y e x t y' e' x' t')
  have "MatchVar y (subst_term t e x) = MatchVar y' (subst_term t' e' x')" using Abs_sumC[OF 79(5,6) eqvt_at_term[OF 79(1)] eqvt_at_term[OF 79(2)]] 79(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
next
  case (81 tys vals e x D t tys' vals' e' x' D' t')
  have "MatchCtor D tys vals (subst_term t e x) = MatchCtor D' tys' vals' (subst_term t' e' x')" using Abs_sumC_star[OF 81(5,6) eqvt_at_term[OF 81(1)] eqvt_at_term[OF 81(2)]] 81(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_def, symmetric, unfolded fun_eq_iff])
} qed (auto simp: eqvt_def subst_term_subst_alt_list_subst_alt_graph_aux_def)
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
  then show ?case proof(cases t rule: \<tau>.strong_exhaust[of _ _ "(\<tau>, a)"])
    case (TyForall x51 x52 x53)
    then show ?thesis using 3(5) P fresh_star_def by blast
  qed (auto simp: 3)
next
  case (18 b \<tau> a k \<sigma> b' \<tau>' a' k' \<sigma>')
  then show ?case using Abs_sumC[OF 18(5,6,1,2)] by fastforce
qed (auto simp: eqvt_def subst_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (case_sum (\<lambda>x. Inr (Inl undefined)) (\<lambda>x. Inr (Inr undefined)))")
  subst_term_type :: "term \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> term" and
  subst_alt_list_type :: "alt_list \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> alt_list" and
  subst_alt_type :: "alt \<Rightarrow> \<tau> \<Rightarrow> tyvar \<Rightarrow> alt" where

  "subst_term_type (Var x) _ _ = Var x"
| "subst_term_type (Ctor D) _ _ = Ctor D"
| "subst_term_type (App e1 e2) \<tau> a = App (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"
| "subst_term_type (TApp e \<tau>2) \<tau> a = TApp (subst_term_type e \<tau> a) (subst_type \<tau>2 \<tau> a)"
| "subst_term_type (Case e alts) \<tau> a = Case (subst_term_type e \<tau> a) (subst_alt_list_type alts \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<lambda> y:\<tau>'. e2) \<tau> a = (\<lambda> y:(subst_type \<tau>' \<tau> a). subst_term_type e2 \<tau> a)"
| "atom b \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (\<Lambda> b:k. e2) \<tau> a = (\<Lambda> b:k. subst_term_type e2 \<tau> a)"
| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_term_type (Let y \<tau>' e1 e2) \<tau> a = Let y (subst_type \<tau>' \<tau> a) (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a)"

| "subst_alt_list_type ANil _ _ = ANil"
| "subst_alt_list_type (ACons alt alts) \<tau> a = ACons (subst_alt_type alt \<tau> a) (subst_alt_list_type alts \<tau> a)"

| "atom y \<sharp> (\<tau>, a) \<Longrightarrow> subst_alt_type (MatchVar y e) \<tau> a = MatchVar y (subst_term_type e \<tau> a)"
| "set (map atom tys @ map atom vals) \<sharp>* (\<tau>, a) \<Longrightarrow> subst_alt_type (MatchCtor D tys vals e) \<tau> a = MatchCtor D tys vals (subst_term_type e \<tau> a)"
proof goal_cases

  (* this is adapted and simplified from here: https://www.joachim-breitner.de/thesis/isa/Substitution.thy *)
  have eqvt_at_term: "\<And>e y z . eqvt_at subst_term_type_subst_alt_list_type_subst_alt_type_sumC (Inl (e, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_term_type a b c) (e, y, z)"
    apply (simp add: eqvt_at_def subst_term_type_def)
    apply rule
    apply (subst Projl_permute)
     apply (simp add: subst_term_type_subst_alt_list_type_subst_alt_type_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_term_type_subst_alt_list_type_subst_alt_type_graph (Inl (e, y, z)))")
      apply(auto)[2]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_term_type_subst_alt_list_type_subst_alt_type_graph.cases)
               apply(assumption)
              apply blast+
    apply simp
    done

{ case (3 P x)
  then show ?case
  proof (cases x)
    case (Inl a)
    then obtain t e y where P: "a = (t, e, y)" by (metis prod.exhaust)
    then show ?thesis using 3(1-5) Inl
    proof (cases t rule: term_alt_list_alt.strong_exhaust(1)[of _ _ "(e, y)"])
      case Lam
      then show ?thesis using 3(6) Inl P fresh_star_insert by blast
    next
      case TyLam
      then show ?thesis using 3(7) Inl P fresh_star_insert by blast
    next
      case Let
      then show ?thesis using 3(8) Inl P fresh_star_insert by blast
    qed auto
  next
    case outer: (Inr b)
    then show ?thesis
    proof (cases b)
      case (Inl a)
      then obtain xs e y where "a = (xs, e, y)" by (metis prod.exhaust)
      then show ?thesis using 3(9,10) Inl outer by (cases xs rule: term_alt_list_alt.exhaust(2)) auto
    next
      case (Inr c)
      then obtain m e y where P: "c = (m, e, y)" by (metis prod.exhaust)
      then show ?thesis using Inr outer 3(11,12)
        apply (cases m rule: term_alt_list_alt.strong_exhaust(3)[of "(e, y)"]) apply simp
        using fresh_star_insert by blast
    qed
  qed
next
  case (54 y \<tau> a \<tau>2 e2 y' \<tau>' a' \<tau>2' e2')
  have "(\<lambda> y : subst_type \<tau>2 \<tau> a . subst_term_type e2 \<tau> a) = (\<lambda> y' : subst_type \<tau>2' \<tau>' a' . subst_term_type e2' \<tau>' a')" using Abs_sumC[OF 54(5,6) eqvt_at_term[OF 54(1)] eqvt_at_term[OF 54(2)]] 54(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (61 b \<tau> a k e2 b' \<tau>' a' k' e2')
  have "(\<Lambda> b : k . subst_term_type e2 \<tau> a) = (\<Lambda> b' : k' . subst_term_type e2' \<tau>' a')" using Abs_sumC[OF 61(5,6) eqvt_at_term[OF 61(1)] eqvt_at_term[OF 61(2)]] 61(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (67 y \<tau> a \<tau>2 e1 e2 y' \<tau>' a' \<tau>2' e1' e2')
  have "Let y (subst_type \<tau>2 \<tau> a) (subst_term_type e1 \<tau> a) (subst_term_type e2 \<tau> a) = Let y' (subst_type \<tau>2' \<tau>' a') (subst_term_type e1' \<tau>' a') (subst_term_type e2' \<tau>' a')"
    using Abs_sumC[OF 67(9,10) eqvt_at_term[OF 67(2)] eqvt_at_term[OF 67(4)]] 67(11) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (79 y \<tau> a e y' \<tau>' a' e')
  have "MatchVar y (subst_term_type e \<tau> a) = MatchVar y' (subst_term_type e' \<tau>' a')" using Abs_sumC[OF 79(5,6) eqvt_at_term[OF 79(1)] eqvt_at_term[OF 79(2)]] 79(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
next
  case (81 tys vals \<tau> a D e tys' vals' \<tau>' a' D' e')
  have "MatchCtor D tys vals (subst_term_type e \<tau> a) = MatchCtor D' tys' vals' (subst_term_type e' \<tau>' a')" using Abs_sumC_star[OF 81(5,6) eqvt_at_term[OF 81(1)] eqvt_at_term[OF 81(2)]] 81(7) by fastforce
  then show ?case by (auto simp: Abs_fresh_iff meta_eq_to_obj_eq[OF subst_term_type_def, symmetric, unfolded fun_eq_iff])
} qed (auto simp: eqvt_def subst_term_type_subst_alt_list_type_subst_alt_type_graph_aux_def)
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
  subst subst_term subst_alt_list subst_alt subst_type subst_term_type subst_alt_list_type subst_alt_type subst_context

end
