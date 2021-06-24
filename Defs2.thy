theory Defs2
  imports Lemmas
begin

nominal_function ctor_data_app_subst :: "\<tau> \<Rightarrow> bool" where
  "ctor_data_app_subst (TyVar _) = False"
| "ctor_data_app_subst (TyData _) = True"
| "ctor_data_app_subst TyArrow = False"
| "ctor_data_app_subst (TyApp \<tau>1 _) = ctor_data_app_subst \<tau>1"
| "ctor_data_app_subst (TyForall _ _ _) = False"
proof goal_cases
  case (3 P x)
  then show ?case by (cases x rule: \<tau>.exhaust) auto
qed (auto simp: eqvt_def ctor_data_app_subst_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function ctor_args :: "\<tau> \<Rightarrow> \<tau> list option" where
  "ctor_args (TyVar _) = None"
| "ctor_args (TyData T) = Some []"
| "ctor_args TyArrow = None"
| "ctor_args (TyApp (TyApp TyArrow \<tau>1) \<tau>2) = (case ctor_args \<tau>2 of
    Some tys \<Rightarrow> Some (\<tau>1#tys)
  | None \<Rightarrow> None)"
| "\<nexists>\<tau>1'. \<tau>1 = TyApp TyArrow \<tau>1' \<Longrightarrow> ctor_args (TyApp \<tau>1 \<tau>2) = (if ctor_data_app_subst (TyApp \<tau>1 \<tau>2) then Some [] else None)"
| "ctor_args (TyForall _ _ _) = None"
proof goal_cases
  case 1
  then show ?case by (auto simp: eqvt_def ctor_args_graph_aux_def split!: option.splits)
next
  case (3 P x)
  then show ?case
  proof (cases x rule: \<tau>.exhaust)
    case (TyApp \<tau>1 \<tau>2)
    then show ?thesis using 3 by (cases "\<exists>\<tau>1'. \<tau>1 = TyApp TyArrow \<tau>1'") auto
  qed auto
qed auto
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_ctor :: "\<tau> \<Rightarrow> \<tau> list \<Rightarrow> \<tau> list option" where
  "subst_ctor (TyVar _) _ = None"
| "subst_ctor TyArrow _ = None"
| "subst_ctor (TyData _) [] = Some []"
| "subst_ctor (TyData _) (_#_) = None"
| "subst_ctor (TyApp \<tau>1 \<tau>2) [] = ctor_args (TyApp \<tau>1 \<tau>2)"
| "subst_ctor (TyApp _ _) (_#_) = None"
| "subst_ctor (TyForall _ _ _) [] = None"
| "subst_ctor (TyForall a _ e) (\<tau>#\<tau>s) = subst_ctor e[\<tau>/a] \<tau>s"
proof goal_cases
  case (3 P x)
  then obtain t xs where P: "x = (t, xs)" by fastforce
  then show ?case using 3
  proof (cases t rule: \<tau>.exhaust)
    case TyData
    then show ?thesis using P 3 by (cases xs) auto
  next
    case TyApp
    then show ?thesis using P 3 by (cases xs) auto
  next
    case TyForall
    then show ?thesis using P 3 by (cases xs) auto
  qed auto
next
  case (39 a k e \<tau> \<tau>s a' k' e' \<tau>' \<tau>s')
  then show ?case by (metis Pair_inject \<tau>.eq_iff(5) list.inject subst_same(2))
qed (auto simp: eqvt_def subst_ctor_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

lemma supp_ctor_args: "ctor_args \<tau> = Some args \<Longrightarrow> supp args \<subseteq> supp \<tau>"
proof (induction \<tau> arbitrary: args rule: ctor_args.induct)
  case (2 T)
  then show ?case unfolding \<tau>.supp(2) pure_supp using supp_Nil by simp
next
  case (4 \<tau>1 \<tau>2)
  then show ?case apply (auto split!: option.splits) unfolding \<tau>.supp supp_Cons by auto
next
  case (5 \<tau>1 \<tau>2 a)
  then show ?case using supp_Nil by (auto split!: if_splits)
qed auto

lemma supp_subst_ctor: "subst_ctor \<tau> \<tau>s = Some args \<Longrightarrow> supp args \<subseteq> supp \<tau> \<union> supp \<tau>s"
proof (induction \<tau> \<tau>s arbitrary: args rule: subst_ctor.induct)
  case (3 T)
  then show ?case unfolding \<tau>.supp(2) pure_supp by simp
next
  case (5 \<tau>1 \<tau>2)
  then have "ctor_args (TyApp \<tau>1 \<tau>2) = Some args" by simp
  then show ?case using supp_Nil supp_ctor_args by auto
next
  case (8 a k e \<tau> \<tau>s)
  then have "supp args \<subseteq> supp e[\<tau>/a] \<union> supp \<tau>s" by simp
  then show ?case unfolding \<tau>.supp(5) pure_supp supp_Cons using supp_subst_type by fastforce
qed auto

end