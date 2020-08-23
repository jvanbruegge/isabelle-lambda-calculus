theory Defs
imports Main "Nominal2.Nominal2" "HOL-Eisbach.Eisbach"
begin

atom_decl "name"
nominal_datatype "\<tau>" =
  TyUnit
 | TyArrow "\<tau>" "\<tau>"  ("_ \<rightarrow> _" 50)

nominal_datatype "term" =
   Var "name"
 | Lam x::"name" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | App "term" "term"
 | Unit
 | Let x::"name" "term" e2::"term" binds x in e2

type_synonym "\<Gamma>" = "(name * \<tau>) list"

declare term.fv_defs[simp]

lemma no_vars_in_ty[simp]: "atom x \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto

nominal_function isin :: "name * \<tau> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
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
is_v_of_e :: "term => bool"
where
"is_v_of_e (Var x) = (False)"
| "is_v_of_e (\<lambda> x : \<tau> . e) = ((True))"
| "is_v_of_e (App e1 e2) = (False)"
| "is_v_of_e Unit = ((True))"
| "is_v_of_e (Let x e1 e2) = (False)"
  apply (all_trivials)
  apply (simp add: eqvt_def is_v_of_e_graph_aux_def)
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
subst_term :: "term => name => term => term"
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

ST_BetaI: "\<lbrakk>is_v_of_e v\<rbrakk> \<Longrightarrow>
((App  (\<lambda> x : \<tau> . e)  v) \<longrightarrow>  subst_term  v   x   e )"

| ST_AppI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App e1 e) \<longrightarrow> (App e2 e))"

| ST_App2I: "\<lbrakk>is_v_of_e v ;
(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App v e1) \<longrightarrow> (App v e2))"

| ST_SubstI: "\<lbrakk>is_v_of_e v\<rbrakk> \<Longrightarrow>
((Let x v e) \<longrightarrow>  subst_term  v   x   e )"

| ST_LetI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((Let x e1 e) \<longrightarrow> (Let x e2 e))"

equivariance Step
nominal_inductive Step .

end