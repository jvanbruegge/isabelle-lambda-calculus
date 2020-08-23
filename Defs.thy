(* generated by Ott 0.31 from: ott/small_step.ott ott/typing.ott ott/grammar.ott *)
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



declare term.fv_defs[simp]

lemma no_vars_in_ty[simp]: "atom x \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto

ML \<open>
fun graph_aux_tac ctxt =
  SUBGOAL (fn (subgoal, i) =>
    (case subgoal of
      Const (@{const_name Trueprop}, _) $ (Const (@{const_name eqvt}, _) $ Free (f, _)) =>
        full_simp_tac (
          ctxt addsimps [@{thm eqvt_def}, Proof_Context.get_thm ctxt (f ^ "_def")]) i
    | _ => no_tac))
\<close>

method_setup eqvt_graph_aux =
  \<open>Scan.succeed (fn ctxt : Proof.context => SIMPLE_METHOD' (graph_aux_tac ctxt))\<close>
  "show equivariance of auxilliary graph construction for nominal functions"

method without_alpha_lst methods m =
  (match termI in H [simproc del: alpha_lst]: _ \<Rightarrow> \<open>m\<close>)

method Abs_lst =
  (match premises in
    "atom ?x \<sharp> c" and P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" for c :: "'a::fs" \<Rightarrow>
      \<open>rule Abs_lst1_fcb2' [where c = c, OF P]\<close>
  \<bar> P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" \<Rightarrow> \<open>rule Abs_lst1_fcb2' [where c = "()", OF P]\<close>)

method pat_comp_aux =
  (match premises in
    "x = (_ :: term) \<Longrightarrow> _" for x \<Rightarrow> \<open>rule term.strong_exhaust [where y = x and c = x]\<close>
  \<bar> "x = (Var _, _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "fst x" and c = x]\<close>
  \<bar> "x = (_, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd x" and c = x]\<close>
  \<bar> "x = (_, _, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule term.strong_exhaust [where y = "snd (snd x)" and c = x]\<close>)

method pat_comp = (pat_comp_aux; force simp: fresh_star_def fresh_Pair_elim)

method freshness uses fresh =
  (match conclusion in
    "_ \<sharp> _" \<Rightarrow> \<open>simp add: fresh_Unit fresh_Pair fresh\<close>
  \<bar> "_ \<sharp>* _" \<Rightarrow> \<open>simp add: fresh_star_def fresh_Unit fresh_Pair fresh\<close>)

method solve_eqvt_at =
  (simp add: eqvt_at_def; simp add: perm_supp_eq fresh_star_Pair)+

method nf uses fresh = without_alpha_lst \<open>
  eqvt_graph_aux, rule TrueI, pat_comp, Abs_lst,
  auto simp: Abs_fresh_iff pure_fresh perm_supp_eq,
  (freshness fresh: fresh)+,
  solve_eqvt_at?\<close>

type_synonym "\<Gamma>" = "(name * \<tau>) list"

nominal_function isin :: "name * \<tau> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (infixr "\<in>" 80) where
  "isin _ [] = False"
| "isin (x, t) ((y, t')#xs) = (if x = y then t = t' else isin (x, t) xs)"
       apply(eqvt_graph_aux)
      apply simp
     apply (metis list.exhaust old.prod.exhaust)
    apply simp
   apply fast
  apply fast
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
  using [[simproc del: alpha_lst]]
  apply(eqvt_graph_aux) apply(blast) apply(pat_comp_aux) apply(auto simp add: fresh_star_def)
  done
nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_PairE: "(a \<sharp> (x, y) \<Longrightarrow> P) \<Longrightarrow> (a \<sharp> x \<Longrightarrow> a \<sharp> y \<Longrightarrow> P)"
  by simp

(** substitutions *)
nominal_function
esubst_e :: "term => name => term => term"
where
"esubst_e e_5 x5 (Var x) = ((if x=x5 then e_5 else (Var x)))"
| "atom x \<sharp> (x5, e_5) \<Longrightarrow> esubst_e e_5 x5 (\<lambda> x : \<tau> . e) = (Lam x \<tau> (esubst_e e_5 x5 e))"
| "esubst_e e_5 x5 (App e1 e2) = (App (esubst_e e_5 x5 e1) (esubst_e e_5 x5 e2))"
| "esubst_e e_5 x5 Unit = (Unit )"
| "atom x \<sharp> (x5, e_5) \<Longrightarrow> esubst_e e_5 x5 (Let x e1 e2) = (Let x (esubst_e e_5 x5 e1) (esubst_e e_5 x5 e2))"
                   apply(eqvt_graph_aux, rule TrueI)
                 apply(simp_all) apply(pat_comp_aux)
        apply(auto simp: fresh_star_def fresh_Pair)
     apply blast
    apply blast
   apply (auto simp: eqvt_at_def)
   apply (metis flip_fresh_fresh)+
  done
nominal_termination (eqvt) by lexicographic_order

lemma fresh_esubst_e: "\<lbrakk> atom z \<sharp> s ; z = y \<or> atom z \<sharp> t \<rbrakk> \<Longrightarrow> atom z \<sharp> esubst_e s y t"
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
  apply (induction \<Gamma>)
   apply simp
  apply (auto simp: fresh_Pair fresh_Cons fresh_at_base(2))
  done

equivariance T
nominal_inductive T avoids
  T_AbsI: x
  | T_LetI: x
     apply auto
  apply freshness+
  done
  

(** definitions *)
(* defns Jst *)
inductive Step :: "term \<Rightarrow> term \<Rightarrow> bool"
and   "Step'" :: "term => term =>  bool" ("_ \<longrightarrow> _" 50)
where
  "(e \<longrightarrow> e') == Step (e) (e')"

| (* defn Step *)

ST_BetaI: "\<lbrakk>is_v_of_e v\<rbrakk> \<Longrightarrow>
((App  (\<lambda> x : \<tau> . e)  v) \<longrightarrow>  esubst_e  v   x   e )"

| ST_AppI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App e1 e) \<longrightarrow> (App e2 e))"

| ST_App2I: "\<lbrakk>is_v_of_e v ;
(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((App v e1) \<longrightarrow> (App v e2))"

| ST_SubstI: "\<lbrakk>is_v_of_e v\<rbrakk> \<Longrightarrow>
((Let x v e) \<longrightarrow>  esubst_e  v   x   e )"

| ST_LetI: "\<lbrakk>(e1 \<longrightarrow> e2)\<rbrakk> \<Longrightarrow>
((Let x e1 e) \<longrightarrow> (Let x e2 e))"

equivariance Step
nominal_inductive Step .
end



