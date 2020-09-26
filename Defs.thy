theory Defs
imports Main "Nominal2.Nominal2" "HOL-Eisbach.Eisbach"
begin

atom_decl "var"
atom_decl "tyvar"

nominal_datatype "\<tau>" =
   TyUnit
   | TyVar "tyvar"
   | TyArrow "\<tau>" "\<tau>"  ("_ \<rightarrow> _" 50)

nominal_datatype "\<sigma>" =
  TyMono "\<tau>"
| TyForall a::"tyvar" t::"\<sigma>" binds a in t

nominal_datatype "term" =
   Var "var"
 | Lam x::"var" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | App "term" "term"
 | Unit
 | Let x::"var" "term" e2::"term" binds x in e2

type_synonym "\<Gamma>" = "(var * \<sigma>) list"

declare term.fv_defs[simp]
declare \<tau>.fv_defs[simp]
declare \<sigma>.fv_defs[simp]

lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto
lemma no_vars_in_ty2[simp]: "atom (x :: var) \<sharp> (ty :: \<sigma>)"
  by (induction ty rule: \<sigma>.induct) auto

nominal_function isin :: "var * \<sigma> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
  "isin _ [] = False"
| "isin (x, t) ((y, t')#xs) = (if x = y then t = t' else isin (x, t) xs)"
       apply (all_trivials)
      apply (simp add: eqvt_def isin_graph_aux_def)
     apply (metis list.exhaust old.prod.exhaust)
    apply simp
  done
nominal_termination (eqvt) by lexicographic_order

(** subrules *)
nominal_function
is_value :: "term => bool"
where
"is_value (Var x) = (False)"
| "is_value (\<lambda> x : \<tau> . e) = ((True))"
| "is_value (App e1 e2) = (False)"
| "is_value Unit = ((True))"
| "is_value (Let x e1 e2) = (False)"
  apply (all_trivials)
  apply (simp add: eqvt_def is_value_graph_aux_def)
  using term.exhaust by blast
nominal_termination (eqvt)
  by lexicographic_order

method pat_comp_aux =
  (match premises in
    "x = (_ :: term) \<Longrightarrow> _" for x \<Rightarrow> \<open>rule term.strong_exhaust [where y = x and c = x]\<close>
  \<bar> "x = (Var _, _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "fst x" and c = x]\<close>
  \<bar> "x = (_, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd x" and c = x]\<close>
  \<bar> "x = (_, _, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd (snd x)" and c = x]\<close>)

(** substitutions *)
nominal_function
subst_term :: "term => var => term => term"
where
"subst_term e_5 x5 (Var x) = ((if x=x5 then e_5 else (Var x)))"
| "atom x \<sharp> (x5, e_5) \<Longrightarrow> subst_term e_5 x5 (\<lambda> x : \<tau> . e) = (Lam x \<tau> (subst_term e_5 x5 e))"
| "subst_term e_5 x5 (App e1 e2) = (App (subst_term e_5 x5 e1) (subst_term e_5 x5 e2))"
| "subst_term e_5 x5 Unit = (Unit )"
| "atom x \<sharp> (x5, e_5) \<Longrightarrow> subst_term e_5 x5 (Let x e1 e2) = (Let x (subst_term e_5 x5 e1) (subst_term e_5 x5 e2))"
                   apply (all_trivials)
        apply (simp add: eqvt_def subst_term_graph_aux_def)
      apply(pat_comp_aux)
          apply(auto simp: fresh_star_def fresh_Pair)
     apply blast
    apply blast
   apply (auto simp: eqvt_at_def)
   apply (metis flip_fresh_fresh)+
  done
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_type :: "\<tau> \<Rightarrow> tyvar \<Rightarrow> \<tau> \<Rightarrow> \<tau>" where
  "subst_type t a TyUnit = TyUnit"
| "subst_type t a (TyArrow \<tau>1 \<tau>2) = TyArrow (subst_type t a \<tau>1) (subst_type t a \<tau>2)"
| "subst_type t a (TyVar y) = (if a = y then t else TyVar y)"
          apply all_trivials
     apply (auto simp: eqvt_def subst_type_graph_aux_def)
  by (meson \<tau>.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

nominal_function subst_types :: "(tyvar * \<tau>) list \<Rightarrow> \<tau> \<Rightarrow> \<tau>" where
  "subst_types [] t = t"
| "subst_types ((a, \<tau>)#xs) t = subst_types xs (subst_type \<tau> a t)"
       apply all_trivials
    apply (auto simp: eqvt_def subst_types_graph_aux_def)
  by (metis neq_Nil_conv surj_pair)
nominal_termination (eqvt) by lexicographic_order

lemma fresh_subst_term: "\<lbrakk> atom z \<sharp> s ; z = y \<or> atom z \<sharp> t \<rbrakk> \<Longrightarrow> atom z \<sharp> subst_term s y t"
  by (nominal_induct t avoiding: z y s rule: term.strong_induct) auto

nominal_function split_vars :: "\<sigma> \<Rightarrow> tyvar list * \<tau>" where
  "split_vars (TyMono \<tau>) = ([], \<tau>)"
| "split_vars (TyForall a \<sigma>) = (let (xs, \<tau>) = split_vars \<sigma> in (a#xs, \<tau>))"
       apply (auto simp: eqvt_def split_vars_graph_aux_def)
   apply (meson \<sigma>.strong_exhaust)
  apply (auto split: prod.splits)
  sorry
nominal_termination (eqvt) by lexicographic_order

definition ty_leq :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> bool" ("_ \<sqsubseteq> _" 50) where
  "ty_leq \<sigma> \<sigma>' = (
    let (as, \<tau>) = split_vars \<sigma> in
    let (bs, \<tau>') = split_vars \<sigma>' in
    (atom ` set bs) \<sharp>* \<sigma> \<and> (\<exists>ts. \<tau>' = subst_types (zip as ts) \<tau>)
  )"

(** definitions *)
(* defns Jwf *)
inductive T :: "\<Gamma> \<Rightarrow> term \<Rightarrow> \<sigma> \<Rightarrow> bool"
and   "T'" :: "\<Gamma> => term => \<sigma> =>  bool" ("_ \<turnstile> _ : _" 50)
where
  "(\<Gamma> \<turnstile> e : \<tau>) == T (\<Gamma>) (e) (\<tau>)"

| (* defn T *)

T_UnitI: "(\<Gamma> \<turnstile> Unit : TyMono TyUnit)"

| T_VarI: "\<lbrakk> isin ( x ,  \<sigma> )  \<Gamma> \<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile> (Var x) : \<sigma>)"

| T_AbsI: "\<lbrakk>atom (x :: var) \<sharp> \<Gamma> ; ( ( x ,  TyMono \<tau>1 ) # \<Gamma>  \<turnstile> e : TyMono \<tau>2)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile>  (\<lambda> x : \<tau>1 . e)  : TyMono (\<tau>1 \<rightarrow> \<tau>2))"

| T_AppI: "\<lbrakk>(\<Gamma> \<turnstile> e1 : TyMono (\<tau>1 \<rightarrow> \<tau>2)) ;
(\<Gamma> \<turnstile> e2 : TyMono \<tau>1)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile> (App e1 e2) : TyMono \<tau>2)"

| T_LetI: "\<lbrakk>atom x \<sharp> (\<Gamma>, e1) ;
( ( x ,  \<sigma> ) # \<Gamma>  \<turnstile> e2 : TyMono \<tau>) ; (\<Gamma> \<turnstile> e1 : \<sigma>)\<rbrakk> \<Longrightarrow>
(\<Gamma> \<turnstile>  (Let x e1 e2)  : TyMono \<tau>)"

| T_InsI: "\<lbrakk> \<Gamma> \<turnstile> e : \<sigma>' ; \<sigma>' \<sqsubseteq> \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e : \<sigma>"

| T_GenI: "\<lbrakk> \<Gamma> \<turnstile> e : \<sigma> ; atom (a :: tyvar) \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e : TyForall a \<sigma>"

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