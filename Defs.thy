theory Defs
imports Main "Nominal2.Nominal2" "HOL-Eisbach.Eisbach"
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
 | Lam x::"var" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | TyLam a::"tyvar" e::"term" binds a in e ("\<Lambda> _ . _" 50)
 | App "term" "term"
 | TyApp "term" "\<tau>"
 | Unit
 | Let x::"var" "term" e2::"term" binds x in e2

type_synonym "\<Gamma>" = "(var * \<tau>) list"

declare term.fv_defs[simp]

lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto

nominal_function isin :: "var * \<tau> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
  "isin _ [] = False"
| "isin (x, t) ((y, t')#xs) = (if x = y then t = t' else isin (x, t) xs)"
       apply (all_trivials)
      apply (simp add: eqvt_def isin_graph_aux_def)
     apply (metis list.exhaust prod.exhaust)
    apply simp
  done
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
| "is_value (Let x e1 e2) = False"
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
nominal_function subst_term :: "term => var => term => term"
where
"subst_term e x (Var y) = (if x=y then e else Var y)"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (\<lambda> y : \<tau> . e2) = (Lam y \<tau> (subst_term e x e2))"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (\<Lambda> y . e2) = (\<Lambda> y . subst_term e x e2)"
| "subst_term e x (App e1 e2) = (App (subst_term e x e1) (subst_term e x e2))"
| "subst_term e x (TyApp e1 \<tau>) = (TyApp (subst_term e x e1) \<tau>)"
| "subst_term _ _ Unit = Unit"
| "atom y \<sharp> (x, e) \<Longrightarrow> subst_term e x (Let y e1 e2) = (Let y (subst_term e x e1) (subst_term e x e2))"
proof goal_cases
next
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
    using Abs_lst_rename_deep[OF c(1) 11(5) sort_same_y 11(1)] term.eq_iff(2) by blast
  have 2: "(\<lambda> y' : \<tau>' . subst_term_sumC (e', x', e2')) = (\<lambda> c : \<tau> . subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 11(6) sort_same_y' 11(2)] term.eq_iff(2) 11(7) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 11(7) by force

  show ?case using 1 2 3 by argo
next
  case (17 y x e e2 y' x' e' e2')
  
  obtain c::tyvar where "atom c \<sharp> (y, y',  e, x, e', x', e2, e2', subst_term_sumC (e, x, e2), subst_term_sumC (e', x', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_sumC (e, x, e2), x, e)" "atom c \<sharp> (subst_term_sumC (e', x', e2'), x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  have 1: "(\<Lambda> y . subst_term_sumC (e, x, e2)) = (\<Lambda> c . subst_term_sumC (e, x, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 17(5) sort_same_y 17(1)] term.eq_iff(3) by presburger
  have 2: "(\<Lambda> y' . subst_term_sumC (e', x', e2')) = (\<Lambda> c . subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
    using Abs_lst_rename_deep[OF c(2) 17(6) sort_same_y' 17(2)] term.eq_iff(3) 17(7) by auto
  have 3: "(y \<leftrightarrow> c) \<bullet> e2 = (y' \<leftrightarrow> c) \<bullet> e2'" using Abs_lst_rename_both[OF c(3) sort_same_y sort_same_y'] 17(7) by force

  show ?case using 1 2 3 by argo
next
  case (31 y x e e1 e2 y' x' e' e1' e2')

  obtain c::var where "atom c \<sharp> (y, y',  e, x, e', x', e2, e2', subst_term_sumC (e, x, e2), subst_term_sumC (e', x', e2'))" using obtain_fresh by blast
  then have c: "atom c \<sharp> (subst_term_sumC (e, x, e2), x, e)" "atom c \<sharp> (subst_term_sumC (e', x', e2'), x', e')" "atom c \<sharp> (y, e2, y', e2')" using fresh_Pair by fastforce+

  have sort_same_y: "sort_of (atom c) = sort_of (atom y)" by simp
  have sort_same_y': "sort_of (atom c) = sort_of (atom y')" by simp

  let ?e1 = "subst_term_sumC (e, x, e1)"
  let ?e1' = "subst_term_sumC (e', x', e1')"
  have 0: "?e1 = ?e1'" using 31 by simp
  have 1: "Let y ?e1 (subst_term_sumC (e, x, e2)) = Let c ?e1 (subst_term_sumC (e, x, (y \<leftrightarrow> c) \<bullet> e2))"
    using Abs_lst_rename_deep[OF c(1) 31(9) sort_same_y 31(2)] 0 term.eq_iff(6) by fastforce
  have 2: "Let y' ?e1' (subst_term_sumC (e', x', e2')) = Let c ?e1 (subst_term_sumC (e, x, (y' \<leftrightarrow> c) \<bullet> e2'))"
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
    using Abs_lst_rename_deep[OF c(1) fresh(1) sort_same_b 13(1)] \<tau>.eq_iff(4) by blast
  have 2: "(\<forall> b' . subst_type_sumC (\<tau>', a', \<sigma>')) = (\<forall> c . subst_type_sumC (\<tau>, a, (b' \<leftrightarrow> c) \<bullet> \<sigma>'))"
    using Abs_lst_rename_deep[OF c(2) fresh(2) sort_same_b' 13(2)] \<tau>.eq_iff(4) 13(7) by blast
  have 3: "(b \<leftrightarrow> c) \<bullet> \<sigma> = (b' \<leftrightarrow> c) \<bullet> \<sigma>'" using Abs_lst_rename_both[OF c(3) sort_same_b sort_same_b'] 13(7) by fastforce

  show ?case using 1 2 3 by argo
qed (auto simp: eqvt_def subst_type_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

lemma fresh_subst_term: "\<lbrakk> atom z \<sharp> s ; z = y \<or> atom z \<sharp> t \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_term s y t"
  by (nominal_induct t avoiding: z y s rule: term.strong_induct) auto

(** definitions *)
(* defns Jwf *)
inductive T :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<tau> \<Rightarrow> bool"
and   "T'" :: "\<Gamma> => term => \<tau> =>  bool" ("_ \<turnstile> _ : _" 50)
where
  "(\<Gamma> \<turnstile> e : \<tau>) == T (\<Gamma>) (e) (\<tau>)"

| (* defn T *)

T_UnitI: "(\<Gamma> \<turnstile> Unit : TyUnit)"

| T_VarI: "\<lbrakk> isin ( x ,  \<tau> )  \<Gamma> \<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile> (Var x) : \<tau>)"

| T_AbsI: "\<lbrakk>atom x \<sharp> \<Gamma> ; ( ( x ,  \<tau>1 ) # \<Gamma>  \<turnstile> e : \<tau>2)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile>  (\<lambda> x : \<tau>1 . e)  : (\<tau>1 \<rightarrow> \<tau>2))"

| T_AppI: "\<lbrakk>(\<Gamma> \<turnstile> e1 : (\<tau>1 \<rightarrow> \<tau>2)) ;
(\<Gamma> \<turnstile> e2 : \<tau>1)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile> (App e1 e2) : \<tau>2)"

| T_LetI: "\<lbrakk>atom x \<sharp> (\<Gamma>, e1) ;
( ( x ,  \<tau>1 ) # \<Gamma>  \<turnstile> e2 : \<tau>2) ; (\<Gamma> \<turnstile> e1 : \<tau>1)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile>  (Let x e1 e2)  : \<tau>2)"

(*| T_InstI: "\<lbrakk> \<Gamma> \<turnstile> e : (\<forall>a . \<sigma>) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> " *)

lemma fresh_not_isin: "atom x \<sharp> \<Gamma> \<Longrightarrow> \<nexists>t'. isin (x, t') \<Gamma>"
  by (induction \<Gamma>) (auto simp: fresh_Pair fresh_Cons fresh_at_base(2))

equivariance T
nominal_inductive T avoids
  T_AbsI: x
  | T_LetI: x
  by (auto simp: fresh_star_def fresh_Unit fresh_Pair)

(** definitions *)
(* defns Jst *)
inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool"
and   "Step'" :: "term => term =>  bool" ("_ \<longrightarrow> _" 50)
where
  "(e \<longrightarrow> e') == Step (e) (e')"

| (* defn Step *)

ST_BetaI: "\<lbrakk>is_value v\<rbrakk> \<Longrightarrow>
((App  (\<lambda> x : \<tau> . e)  v) \<longrightarrow>  subst_term  v   x   e )"

| ST_AppI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App e1 e) \<longrightarrow> (App e2 e))"

| ST_App2I: "\<lbrakk>is_value v ;
(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App v e1) \<longrightarrow> (App v e2))"

| ST_SubstI: "\<lbrakk>is_value v\<rbrakk> \<Longrightarrow>
((Let x v e) \<longrightarrow>  subst_term  v   x   e )"

| ST_LetI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((Let x e1 e) \<longrightarrow> (Let x e2 e))"

equivariance Step
nominal_inductive Step .

end