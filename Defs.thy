theory Defs
imports Main "Nominal2.Nominal2"
begin

atom_decl "var"
atom_decl "tyvar"

nominal_datatype "\<tau>" =
  TyUnit
  | TyVar "tyvar"
  | TyArrow "\<tau>" "\<tau>"  ("_ \<rightarrow> _" 50)
  | TyForall a::"tyvar" t::"\<tau>" binds a in t ("\<forall> _ . _" 50)

nominal_datatype "term" =
   Var "var"
 | App "term" "term"
 | TyApp "term" "\<tau>"
 | Unit
 | Lam x::"var" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | TyLam a::"tyvar" e::"term" binds a in e ("\<Lambda> _ . _" 50)
 | Let x::"var" "\<tau>" "term" e2::"term" binds x in e2

nominal_datatype "binder" =
  "BVar" "var" "\<tau>"
  | "BTyVar" "tyvar"

type_synonym "\<Gamma>" = "binder list"

declare term.fv_defs[simp]
declare \<tau>.fv_defs[simp]

lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto

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

(** subrules *)
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

lemma Abs_lst_rename: "\<lbrakk> atom c \<sharp> e ; sort_of (atom c) = sort_of (atom a) \<rbrakk> \<Longrightarrow> [[atom a]]lst. e = [[atom c]]lst. (a \<leftrightarrow> c) \<bullet> e"
proof -
  assume a: "atom c \<sharp> e" and a2: "sort_of (atom c) = sort_of (atom a)"
  then have 1: "atom c \<notin> supp e - set [atom a]" by (simp add: fresh_def)
  have 2: "atom a \<notin> supp e - set [atom a]" by simp
  show ?thesis using Abs_swap2[OF 2 1] by (simp add: a2 flip_def)
qed

lemma Abs_lst_rename_both:
"\<lbrakk> atom c \<sharp> (y, e::'e::fs, y', e'::'e::fs) ; sort_of (atom c) = sort_of (atom y) ; sort_of (atom c) = sort_of (atom y') ; ([[atom y]]lst. e) = ([[atom y']]lst. e') \<rbrakk> \<Longrightarrow>
  (y \<leftrightarrow> c) \<bullet> e = (y' \<leftrightarrow> c) \<bullet> e'"
proof -
  assume a: "atom c \<sharp> (y, e, y', e')" "sort_of (atom c) = sort_of (atom y)" "sort_of (atom c) = sort_of (atom y')" "([[atom y]]lst. e) = ([[atom y']]lst. e')"
  then have "(y \<leftrightarrow> c) \<bullet> ([[atom y]]lst. e) = (y' \<leftrightarrow> c) \<bullet> ([[atom y']]lst. e')"
    by (smt Abs_lst_rename Cons_eqvt Nil_eqvt flip_def fresh_PairD(1) fresh_PairD(2) permute_Abs_lst swap_atom_simps(1))
  then have "([[atom c]]lst. (y \<leftrightarrow> c) \<bullet> e) = ([[atom c]]lst. (y' \<leftrightarrow> c) \<bullet> e')" using Abs_lst_rename a(2) a(3) by auto
  then show ?thesis using Abs1_eq(3) by blast
qed

lemma eqvt_at_deep: "\<lbrakk> atom a \<sharp> (x, e) ; atom c \<sharp> (x, e) ; eqvt_at f (e, x, e2) \<rbrakk> \<Longrightarrow> (a \<leftrightarrow> c) \<bullet> f (e, x, e2) = f (e, x, (a \<leftrightarrow> c) \<bullet> e2)"
proof -
  assume a: "atom a \<sharp> (x, e)" "atom c \<sharp> (x, e)" "eqvt_at f (e, x, e2)"

  have 1: "(a \<leftrightarrow> c) \<bullet> f (e, x, e2) = f ((a \<leftrightarrow> c) \<bullet> (e, x, e2))" using a(3) eqvt_at_def by blast
  have 2: "(a \<leftrightarrow> c) \<bullet> (e, x, e2) = (e, x, (a \<leftrightarrow> c) \<bullet> e2)" using a(1) a(2) fresh_Pair flip_fresh_fresh by fastforce

  show ?thesis using 1 2 by argo
qed

lemma Abs_lst_rename_deep: "\<lbrakk> atom c \<sharp> (f (e, x, e2), x, e) ; atom a \<sharp> (x, e) ; sort_of (atom c) = sort_of (atom a) ; eqvt_at f (e, x, e2) \<rbrakk> \<Longrightarrow> [[atom a]]lst. f (e, x, e2) = [[atom c]]lst. f (e, x, (a \<leftrightarrow> c) \<bullet> e2)"
proof -
  assume a: "atom c \<sharp> (f (e, x, e2), x, e)" "atom a \<sharp> (x, e)" "sort_of (atom c) = sort_of (atom a)" "eqvt_at f (e, x, e2)"

  have 1: "[[atom a]]lst. f (e, x, e2) = [[atom c]]lst. (a \<leftrightarrow> c) \<bullet> f (e, x, e2)" using Abs_lst_rename[OF _ a(3)] a(1) fresh_Pair by blast
  have 2: "(a \<leftrightarrow> c) \<bullet> f (e, x, e2) = f (e, x, (a \<leftrightarrow> c) \<bullet> e2)" using eqvt_at_deep[OF a(2) _ a(4)] a(1) fresh_Pair by blast

  show ?thesis using 1 2 by argo
qed

(** substitutions *)
nominal_function subst_term :: "term => var => term => term" where
  "subst_term e x (Var y) = (if x=y then e else Var y)"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (\<lambda> y : \<tau> . e2) = (Lam y \<tau> (subst_term e x e2))"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (\<Lambda> y . e2) = (\<Lambda> y . subst_term e x e2)"
| "subst_term e x (App e1 e2) = (App (subst_term e x e1) (subst_term e x e2))"
| "subst_term e x (TyApp e1 \<tau>) = (TyApp (subst_term e x e1) \<tau>)"
| "subst_term _ _ Unit = Unit"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (Let y \<tau> e1 e2) = (Let y \<tau> (subst_term e x e1) (subst_term e x e2))"
proof goal_cases
  case (3 P x)
  then obtain e y t where P: "x = (e, y, t)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(y, e)"])
         apply (auto simp: 3)
    using 3(2) 3(3) 3(7) P fresh_star_def by blast+
next
  case (11 y x e \<tau> e2 y' x' e' \<tau>' e2')

  obtain c::var where "atom c \<sharp> (y, y',  e, x, e', x', e2, e2', subst_term_sumC (e, x, e2), subst_term_sumC (e', x', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_sumC (e, x, e2), x, e)" "atom c \<sharp> (subst_term_sumC (e', x', e2'), x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  have 1: "(\<lambda> y : \<tau> . subst_term_sumC (e, x, e2)) = (\<lambda> c : \<tau> . subst_term_sumC (e, x, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 11(5) sort_same_y 11(1)] by auto
  have 2: "(\<lambda> y' : \<tau>' . subst_term_sumC (e', x', e2')) = (\<lambda> c : \<tau> . subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 11(6) sort_same_y' 11(2)] 11(7) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 11(7) by force

  show ?case using 1 2 3 by argo
next
  case (17 y x e e2 y' x' e' e2')

  obtain c::tyvar where "atom c \<sharp> (y, y',  e, x, e', x', e2, e2', subst_term_sumC (e, x, e2), subst_term_sumC (e', x', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_sumC (e, x, e2), x, e)" "atom c \<sharp> (subst_term_sumC (e', x', e2'), x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  have 1: "(\<Lambda> y . subst_term_sumC (e, x, e2)) = (\<Lambda> c . subst_term_sumC (e, x, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 17(5) sort_same_y 17(1)] by auto
  have 2: "(\<Lambda> y' . subst_term_sumC (e', x', e2')) = (\<Lambda> c . subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 17(6) sort_same_y' 17(2)] 17(7) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 17(7) by force

  show ?case using 1 2 3 by argo
next
  case (31 y x e \<tau> e1 e2 y' x' e' \<tau>' e1' e2')

  obtain c::var where "atom c \<sharp> (y, y',  e, x, e', x', e2, e2', subst_term_sumC (e, x, e2), subst_term_sumC (e', x', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_sumC (e, x, e2), x, e)" "atom c \<sharp> (subst_term_sumC (e', x', e2'), x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  let ?e1 = "subst_term_sumC (e, x, e1)"
  let ?e1' = "subst_term_sumC (e', x', e1')"
  have 0: "?e1 = ?e1'" using 31 by simp
  have 1: "Let y \<tau> ?e1 (subst_term_sumC (e, x, e2)) = Let c \<tau> ?e1 (subst_term_sumC (e, x, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 31(9) sort_same_y 31(2)] 0 term.eq_iff(6) by fastforce
  have 2: "Let y' \<tau>' ?e1' (subst_term_sumC (e', x', e2')) = Let c \<tau> ?e1 (subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 31(10) sort_same_y' 31(4)] 0 term.eq_iff(6) 31(11) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 31(11) by force

  show ?case using 1 2 3 by argo
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

  obtain c::tyvar where "atom c \<sharp> (b, b', \<tau>, a, \<tau>', a', \<sigma>, \<sigma>', subst_type_sumC (\<tau>, a, \<sigma>), subst_type_sumC (\<tau>', a', \<sigma>'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_type_sumC (\<tau>, a, \<sigma>), a, \<tau>)" "atom c \<sharp> (subst_type_sumC (\<tau>', a', \<sigma>'), a', \<tau>')" "atom c \<sharp> (b, \<sigma>, b', \<sigma>')" using fresh_Pair by fastforce+

  have sort_same_b: "sort_of (atom c) = sort_of (atom b)" by simp
  have sort_same_b': "sort_of (atom c) = sort_of (atom b')" by simp

  from 13 have fresh: "atom b \<sharp> (a, \<tau>)" "atom b' \<sharp> (a', \<tau>')" using fresh_Pair by fastforce+

  have 1: "(\<forall> b . subst_type_sumC (\<tau>, a, \<sigma>)) = (\<forall> c . subst_type_sumC (\<tau>, a, (b \<leftrightarrow> c) \<bullet> \<sigma>))"
    using Abs_lst_rename_deep[OF c(1) fresh(1) sort_same_b 13(1)] by auto
  have 2: "(\<forall> b' . subst_type_sumC (\<tau>', a', \<sigma>')) = (\<forall> c . subst_type_sumC (\<tau>, a, (b' \<leftrightarrow> c) \<bullet> \<sigma>'))"
    using Abs_lst_rename_deep[OF c(2) fresh(2) sort_same_b' 13(2)] 13(7) by auto
  have 3: "(b \<leftrightarrow> c) \<bullet> \<sigma> = (b' \<leftrightarrow> c) \<bullet> \<sigma>'" using Abs_lst_rename_both[OF c(3) sort_same_b sort_same_b'] 13(7) by fastforce

  show ?case using 1 2 3 by argo
qed (auto simp: eqvt_def subst_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_term_type :: "\<tau> \<Rightarrow> tyvar \<Rightarrow> term \<Rightarrow> term" where
  "subst_term_type _ _ (Var x) = Var x"
| "subst_term_type _ _ Unit = Unit"
| "atom y \<sharp> (a, \<tau>) \<Longrightarrow> subst_term_type \<tau> a (\<lambda> y : \<tau>' . e2) = (Lam y (subst_type \<tau> a \<tau>') (subst_term_type \<tau> a e2))"
| "atom b \<sharp> (a, \<tau>) \<Longrightarrow> subst_term_type \<tau> a (\<Lambda> b . e2) = (TyLam b (subst_term_type \<tau> a e2))"
| "subst_term_type \<tau> a (App e1 e2) = App (subst_term_type \<tau> a e1) (subst_term_type \<tau> a e2)"
| "subst_term_type \<tau> a (TyApp e \<tau>2) = TyApp (subst_term_type \<tau> a e) (subst_type \<tau> a \<tau>2)"
| "atom y \<sharp> (a, \<tau>) \<Longrightarrow> subst_term_type \<tau> a (Let y \<tau>' e1 e2) = Let y (subst_type \<tau> a \<tau>') (subst_term_type \<tau> a e1) (subst_term_type \<tau> a e2)"
proof goal_cases
  case (3 P x)
  then obtain \<tau> a t where P: "x = (\<tau>, a, t)" by (metis prod.exhaust)
  then show ?case
    apply (cases t rule: term.strong_exhaust[of _ _ "(a, \<tau>)"])
    using 3 P apply auto[4]
    using 3(3) 3(4) 3(7) P fresh_star_def by blast+
next
  case (17 y \<tau> a \<tau>2 e y' \<tau>' a' \<tau>2' e')

  obtain c::var where "atom c \<sharp> (y, y', \<tau>, a, \<tau>', a', e, e', subst_term_type_sumC (a, \<tau>, e), subst_term_type_sumC (a', \<tau>', e'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_type_sumC (a, \<tau>, e), \<tau>, a)" "atom c \<sharp> (subst_term_type_sumC (a', \<tau>', e'), \<tau>', a')" "atom c \<sharp> (y, e, y', e')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  have 1: "(\<lambda> y : subst_type a \<tau> \<tau>2 . subst_term_type_sumC (a, \<tau>, e)) = (\<lambda> c : subst_type a \<tau> \<tau>2 . subst_term_type_sumC (a, \<tau>, (y \<leftrightarrow> c) \<bullet> e))"
    using Abs_lst_rename_deep[OF c(1) 17(5) sort_same_y 17(1)] by auto
  have 2: "(\<lambda> y' : subst_type a' \<tau>' \<tau>2' . subst_term_type_sumC (a', \<tau>', e')) = (\<lambda> c : subst_type a' \<tau>' \<tau>2' . subst_term_type_sumC (a, \<tau>, (y' \<leftrightarrow> c) \<bullet> e'))"
    using Abs_lst_rename_deep[OF c(2) 17(6) sort_same_y' 17(2)] 17(7) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e = (y' \<leftrightarrow> c) \<bullet> e'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 17(7) by force
  have 4: "subst_type a \<tau> \<tau>2 = subst_type a' \<tau>' \<tau>2'" using 17(7) by simp

  show ?case using 1 2 3 4 by argo
next
  case (22 b \<tau> a e b' \<tau>' a' e')

  obtain c::tyvar where "atom c \<sharp> (b, b', \<tau>, a, \<tau>', a', e, e', subst_term_type_sumC (a, \<tau>, e), subst_term_type_sumC (a', \<tau>', e'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_type_sumC (a, \<tau>, e), \<tau>, a)" "atom c \<sharp> (subst_term_type_sumC (a', \<tau>', e'), \<tau>', a')" "atom c \<sharp> (b, e, b', e')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom b)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom b')" by simp

  have 1: "(\<Lambda> b . subst_term_type_sumC (a, \<tau>, e)) = (\<Lambda> c . subst_term_type_sumC (a, \<tau>, (b \<leftrightarrow> c) \<bullet> e))"
    using Abs_lst_rename_deep[OF c(1) 22(5) sort_same_y 22(1)] by auto
  have 2: "(\<Lambda> b' . subst_term_type_sumC (a', \<tau>', e')) = (\<Lambda> c . subst_term_type_sumC (a, \<tau>, (b' \<leftrightarrow> c) \<bullet> e'))"
    using Abs_lst_rename_deep[OF c(2) 22(6) sort_same_y' 22(2)] 22(7) by auto
  have 3: "(b \<leftrightarrow> c) \<bullet> e = (b' \<leftrightarrow> c) \<bullet> e'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 22(7) by force

  show ?case using 1 2 3 by argo
next
  case (31 y a \<tau> \<tau>2 e1 e2 y' a' \<tau>' \<tau>2' e1' e2')
  obtain c::var where "atom c \<sharp> (y, y', \<tau>, a, \<tau>', a', e1, e1', e2, e2', subst_term_type_sumC (\<tau>, a, e2), subst_term_type_sumC (\<tau>', a', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_type_sumC (\<tau>, a, e2), a, \<tau>)" "atom c \<sharp> (subst_term_type_sumC (\<tau>', a', e2'), a', \<tau>')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp
  let ?e1 = "subst_term_type_sumC (\<tau>, a, e1)"
  let ?e2 = "subst_term_type_sumC (\<tau>', a', e1')"

  have 1: "Let y (subst_type \<tau> a \<tau>2) ?e1 (subst_term_type_sumC (\<tau>, a, e2)) = Let c (subst_type \<tau> a \<tau>2) ?e1 (subst_term_type_sumC (\<tau>, a, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 31(9) sort_same_y 31(2)] by auto
  have 2: "Let y' (subst_type \<tau>' a' \<tau>2') ?e2 (subst_term_type_sumC (\<tau>', a', e2')) = Let c (subst_type \<tau> a \<tau>2) ?e1 (subst_term_type_sumC (\<tau>, a, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 31(10) sort_same_y' 31(4)] 31(11) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 31(11) by force

  show ?case using 1 2 3 by argo
qed (auto simp: eqvt_def subst_term_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

lemma fresh_subst_term: "\<lbrakk> atom z \<sharp> s ; atom z \<sharp> t \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_term s y t"
  by (nominal_induct t avoiding: z y s rule: term.strong_induct) auto

lemma fresh_subst_type: "\<lbrakk> atom z \<sharp> \<tau> ; atom z \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_type \<tau> a \<sigma>"
  by (nominal_induct \<sigma> avoiding: z a \<tau> rule: \<tau>.strong_induct) auto

lemma fresh_subst_term_type: "\<lbrakk> atom z \<sharp> \<tau> ; atom z \<sharp> e \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_term_type \<tau> a e"
  by (nominal_induct e avoiding: z a \<tau> rule: term.strong_induct) (auto simp: fresh_subst_type)

lemma fresh_after_subst_type: "\<lbrakk> atom a \<sharp> \<tau> \<rbrakk> \<Longrightarrow> atom a \<sharp> subst_type \<tau> a \<sigma>"
  by (nominal_induct \<sigma> avoiding: a \<tau> rule: \<tau>.strong_induct) auto

lemma subst_term_var_name: "atom c \<sharp> (a, e) \<Longrightarrow> subst_term e' a e = subst_term e' c ((a \<leftrightarrow> c) \<bullet> e)"
proof (nominal_induct e avoiding: c a e' rule: term.strong_induct)
  case (Var x)
  then show ?case
    by (smt flip_at_base_simps(3) flip_at_simps(2) flip_fresh_fresh fresh_PairD(1) fresh_PairD(2) fresh_at_base_permute_iff subst_term.simps(1) term.fresh(1) term.perm_simps(1))
next
  case (Let x e1 e2)
  then show ?case
    by (smt flip_fresh_fresh fresh_Pair fresh_at_base(2) list.set(1) list.set(2) no_vars_in_ty singletonD subst_term.simps(7) term.fresh(7) term.perm_simps(7))
qed (auto simp: flip_fresh_fresh fresh_Pair fresh_at_base(2))

lemma subst_type_var_name: "atom c \<sharp> (a, \<tau>) \<Longrightarrow> subst_type \<tau>' a \<tau> = subst_type \<tau>' c ((a \<leftrightarrow> c) \<bullet> \<tau>)"
  by (nominal_induct \<tau> avoiding: c a \<tau>' rule: \<tau>.strong_induct) (auto simp: flip_fresh_fresh fresh_Pair fresh_at_base(2))

lemma subst_term_type_var_name: "atom c \<sharp> (a, e) \<Longrightarrow> subst_term_type \<tau>' a e = subst_term_type \<tau>' c ((a \<leftrightarrow> c) \<bullet> e)"
proof (nominal_induct e avoiding: c a \<tau>' rule: term.strong_induct)
  case (Var x)
  then show ?case
    by (metis (full_types) \<tau>.fresh(2) flip_at_simps(1) flip_fresh_fresh fresh_PairD(2) fresh_ineq_at_base no_vars_in_ty subst_term_type.simps(1) term.fresh(1))
next
  case (Lam x1a x2 x3)
  then show ?case
    by (smt flip_fresh_fresh fresh_Pair fresh_at_base(2) list.set(1) list.set(2) singletonD subst_term_type.simps(3) subst_type_var_name term.fresh(5) term.perm_simps(5))
next
  case (Let x1a x2 x3)
  then show ?case
    by (smt flip_fresh_fresh fresh_Pair fresh_at_base(2) list.set(1) list.set(2) singletonD subst_term_type.simps(7) subst_type_var_name term.fresh(7) term.perm_simps(7))
qed (auto simp: flip_fresh_fresh fresh_Pair fresh_at_base(2) subst_type_var_name)

lemma subst_term_det: "[[atom a]]lst. e = [[atom b]]lst. e2 \<Longrightarrow> subst_term e' a e = subst_term e' b e2"
proof -
  assume a: "[[atom a]]lst. e = [[atom b]]lst. e2"
  obtain c::var where P: "atom c \<sharp> (a, e, b, e2)" using obtain_fresh by blast

  have sorta: "sort_of (atom c) = sort_of (atom a)" by simp
  have sortb: "sort_of (atom c) = sort_of (atom b)" by simp

  have 1: "subst_term e' a e = subst_term e' c ((a \<leftrightarrow> c) \<bullet> e)" using subst_term_var_name P by auto
  have 2: "subst_term e' b e2 = subst_term e' c ((b \<leftrightarrow> c) \<bullet> e2)" using subst_term_var_name P by auto

  have 3: "(a \<leftrightarrow> c) \<bullet> e = (b \<leftrightarrow> c) \<bullet> e2" using Abs_lst_rename_both[OF P sorta sortb a] .

  show ?thesis using 1 2 3 by argo
qed

lemma subst_type_det: "[[atom a]]lst. e = [[atom b]]lst. e2 \<Longrightarrow> subst_type \<tau> a e = subst_type \<tau> b e2"
proof -
  assume a: "[[atom a]]lst. e = [[atom b]]lst. e2"
  obtain c::tyvar where P: "atom c \<sharp> (a, e, b, e2)" using obtain_fresh by blast

  have sorta: "sort_of (atom c) = sort_of (atom a)" by simp
  have sortb: "sort_of (atom c) = sort_of (atom b)" by simp

  have 1: "subst_type \<tau> a e = subst_type \<tau> c ((a \<leftrightarrow> c) \<bullet> e)" using subst_type_var_name P by auto
  have 2: "subst_type \<tau> b e2 = subst_type \<tau> c ((b \<leftrightarrow> c) \<bullet> e2)" using subst_type_var_name P by auto

  have 3: "(a \<leftrightarrow> c) \<bullet> e = (b \<leftrightarrow> c) \<bullet> e2" using Abs_lst_rename_both[OF P sorta sortb a] .

  show ?thesis using 1 2 3 by argo
qed

lemma subst_term_type_det: "[[atom a]]lst. e = [[atom b]]lst. e2 \<Longrightarrow> subst_term_type \<tau> a e = subst_term_type \<tau> b e2"
proof -
  assume a: "[[atom a]]lst. e = [[atom b]]lst. e2"
  obtain c::tyvar where P: "atom c \<sharp> (a, e, b, e2)" using obtain_fresh by blast

  have sorta: "sort_of (atom c) = sort_of (atom a)" by simp
  have sortb: "sort_of (atom c) = sort_of (atom b)" by simp

  have 1: "subst_term_type \<tau> a e = subst_term_type \<tau> c ((a \<leftrightarrow> c) \<bullet> e)" using subst_term_type_var_name P by auto
  have 2: "subst_term_type \<tau> b e2 = subst_term_type \<tau> c ((b \<leftrightarrow> c) \<bullet> e2)" using subst_term_type_var_name P by auto

  have 3: "(a \<leftrightarrow> c) \<bullet> e = (b \<leftrightarrow> c) \<bullet> e2" using Abs_lst_rename_both[OF P sorta sortb a] .

  show ?thesis using 1 2 3 by argo
qed

inductive Ty :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> bool"
and "Ty'" :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t\<^sub>y _")
where
  "(\<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>) \<equiv> Ty \<Gamma> \<tau>"

| Ty_Unit: "\<Gamma> \<turnstile>\<^sub>t\<^sub>y TyUnit"

| Ty_Var: "\<lbrakk> BTyVar a \<in> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y TyVar a"

| Ty_Arrow: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<tau>1 \<rightarrow> \<tau>2)"

| Ty_Forall: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t\<^sub>y (\<forall>a. \<sigma>)"

equivariance Ty
nominal_inductive Ty avoids
  Ty_Forall: a
  by (auto simp: fresh_star_def fresh_Unit fresh_Pair)

(** definitions *)
(* defns Jwf *)
inductive T :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool"
and   "T'" :: "\<Gamma> => term => \<tau> =>  bool" ("_ \<turnstile> _ : _" 50)
where
  "(\<Gamma> \<turnstile> e : \<tau>) == T (\<Gamma>) (e) (\<tau>)"

| T_UnitI: "(\<Gamma> \<turnstile> Unit : TyUnit)"

| T_VarI: "\<lbrakk> BVar x \<tau> \<in>  \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>"

| T_AbsI: "\<lbrakk>atom x \<sharp> \<Gamma> ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; BVar x \<tau>1 # \<Gamma>  \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda> x : \<tau>1 . e) : (\<tau>1 \<rightarrow> \<tau>2)"

| T_AppI: "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2) ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"

| T_LetI: "\<lbrakk> atom x \<sharp> (\<Gamma>, e1) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau>1 ; BVar x \<tau>1 # \<Gamma> \<turnstile> e2 : \<tau>2 ; \<Gamma> \<turnstile> e1 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Let x \<tau>1 e1 e2 : \<tau>2"

| T_AppTI: "\<lbrakk> \<Gamma> \<turnstile> e : (\<forall>a . \<sigma>) ; \<Gamma> \<turnstile>\<^sub>t\<^sub>y \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> TyApp e \<tau> : subst_type \<tau> a \<sigma>"

| T_AbsTI: "\<lbrakk> BTyVar a # \<Gamma> \<turnstile> e : \<sigma> ; atom a \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (\<Lambda> a . e) : (\<forall> a . \<sigma>)"

lemma fresh_not_isin_tyvar: "atom a \<sharp> \<Gamma> \<Longrightarrow> \<not>isin (BTyVar a) \<Gamma>"
  apply (induction \<Gamma>)
   apply simp
  by (metis binder.fresh(2) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(4) isin.simps(5))

lemma fresh_not_isin_var: "atom x \<sharp> \<Gamma> \<Longrightarrow> \<nexists>t'. isin (BVar x t') \<Gamma>"
  apply (induction \<Gamma>)
  apply simp
  by (metis (mono_tags, lifting) binder.fresh(1) binder.strong_exhaust fresh_Cons fresh_at_base(2) isin.simps(2) isin.simps(3))

equivariance T
nominal_inductive T avoids
  T_AbsI: x
  | T_LetI: x
  | T_AbsTI: a
  by (auto simp: fresh_star_def fresh_Unit fresh_Pair)

(** definitions *)
(* defns Jst *)
inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool"
and   "Step'" :: "term => term =>  bool" ("_ \<longrightarrow> _" 50)
where
  "(e \<longrightarrow> e') == Step (e) (e')"

| ST_BetaI: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> App (\<lambda> x : \<tau> . e) v \<longrightarrow> subst_term v x e"

| ST_AppI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> App e1 e \<longrightarrow> App e2 e"

| ST_App2I: "\<lbrakk> is_value v ; e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> App v e1 \<longrightarrow> App v e2"

| ST_SubstI: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> Let x \<tau> v e \<longrightarrow> subst_term v x e"

| ST_LetI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> Let x \<tau> e1 e \<longrightarrow> Let x \<tau> e2 e"

| ST_BetaTI: "TyApp (\<Lambda> a . e) \<tau> \<longrightarrow> subst_term_type \<tau> a e"

| ST_AppTI: "\<lbrakk> e1 \<longrightarrow> e2 \<rbrakk> \<Longrightarrow> TyApp e1 \<tau> \<longrightarrow> TyApp e2 \<tau>"

equivariance Step
nominal_inductive Step .

definition beta_nf :: "term \<Rightarrow> bool" where
  "beta_nf e \<equiv> \<nexists>e'. Step e e'"

lemma value_beta_nf: "is_value v \<Longrightarrow> beta_nf v"
  apply (cases v rule: term.exhaust)
  using Step.cases beta_nf_def by fastforce+

lemma Step_deterministic: "\<lbrakk> Step e e1 ; Step e e2 \<rbrakk> \<Longrightarrow> e1 = e2"
proof (induction e e1 arbitrary: e2 rule: Step.induct)
  case (ST_BetaI v x \<tau> e)
  from \<open>App (\<lambda> x : \<tau> . e) v \<longrightarrow> e2\<close> show ?case
  proof (cases rule: Step.cases)
    case (ST_BetaI y t)
    then show ?thesis using subst_term_det by blast
  next
    case (ST_AppI e2)
    then show ?thesis using Step.cases by fastforce
  next
    case (ST_App2I e2')
    then show ?thesis using ST_BetaI.hyps value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_AppI e1 e2 e)
  from \<open>App e1 e \<longrightarrow> e2\<close> show ?case
    apply cases
    using ST_AppI Step.cases value_beta_nf beta_nf_def by fastforce+
next
  case (ST_App2I v e1 e2)
  from \<open>App v e1 \<longrightarrow> e2\<close> show ?case
    apply cases
    using ST_App2I.hyps(2) value_beta_nf beta_nf_def apply blast
    using ST_App2I.hyps(1) value_beta_nf beta_nf_def apply blast
    using ST_App2I value_beta_nf beta_nf_def by auto
next
  case (ST_SubstI v x e)
  from ST_SubstI(2) show ?case
  proof cases
    case (ST_SubstI x e)
    then show ?thesis using subst_term_det by blast
  next
    case (ST_LetI e2 x e)
    then show ?thesis using ST_SubstI.hyps value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_LetI t1 t2 x \<tau> e)
  from \<open>Let x \<tau> t1 e \<longrightarrow> e2\<close> show ?case
    apply cases
    using ST_LetI value_beta_nf beta_nf_def by auto
next
  case (ST_BetaTI a e \<tau>)
  then show ?case
  proof cases
    case (ST_BetaTI b e')
    then show ?thesis using subst_term_type_det by blast
  next
    case (ST_AppTI e2)
    then show ?thesis using is_value.simps(3) value_beta_nf beta_nf_def by blast
  qed
next
  case (ST_AppTI e1 e2 \<tau>)
  from \<open>TyApp e1 \<tau> \<longrightarrow> e2\<close> show ?case
    apply cases
    using ST_AppTI value_beta_nf beta_nf_def by auto
qed

end