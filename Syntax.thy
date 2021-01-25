theory Syntax
  imports "Nominal2.Nominal2"
begin

atom_decl "var"
atom_decl "tyvar"

atom_decl "data_name"
atom_decl "ctor_name"

nominal_datatype "\<kappa>" =
  Star ("\<star>")
  | KArrow "\<kappa>" "\<kappa>" (infixr "\<rightarrow>" 50)

nominal_datatype "\<tau>" =
  TyVar "tyvar"
  | TyData "data_name" tlist
  | TyArrow
  | TyApp "\<tau>" "\<tau>"
  | TyForall a::"tyvar" "\<kappa>" t::"\<tau>" binds a in t ("\<forall> _ : _ . _" 50)
and tlist = TNil | TCons \<tau> tlist

abbreviation arrow_app :: "\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<rightarrow>" 50) where
  "arrow_app \<tau>1 \<tau>2 \<equiv> TyApp (TyApp TyArrow \<tau>1) \<tau>2"

nominal_datatype "term" =
   Var "var"
 | App "term" "term"
 | TApp "term" "\<tau>"
 | Ctor "ctor_name" tlist elist
 | Lam x::"var" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | TyLam a::"tyvar" "\<kappa>" e::"term" binds a in e ("\<Lambda> _ : _ . _" 50)
 | Let x::"var" "\<tau>" "term" e2::"term" binds x in e2
and elist = ENil | ECons "term" elist

nominal_datatype "binder" =
  BVar "var" "\<tau>"
  | BTyVar "tyvar" "\<kappa>"

nominal_datatype "axiom" =
  AxData "data_name" "\<kappa>"
  | AxCtor "ctor_name" "\<tau>"

type_synonym "\<Gamma>" = "binder list"
type_synonym "\<Delta>" = "axiom list"

lemma no_vars_in_kinds[simp]: "atom (x :: var) \<sharp> (k :: \<kappa>)"
  by (induction k rule: \<kappa>.induct) auto
lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (ty :: \<tau>) \<and> atom x \<sharp> (tys :: tlist)"
  by (induction rule: \<tau>_tlist.induct) auto
lemma no_vars_in_axioms[simp]: "atom (x :: var) \<sharp> (\<Delta> :: \<Delta>)"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case by (cases a rule: axiom.exhaust) (auto simp: fresh_Cons)
qed (rule fresh_Nil)

lemma perm_axioms_vars[simp]: "((a::var) \<leftrightarrow> b) \<bullet> (\<Delta>::\<Delta>) = \<Delta>"
  using flip_fresh_fresh by force
lemma perm_\<tau>_vars[simp]: "((a::var) \<leftrightarrow> b) \<bullet> (\<tau>::\<tau>) = \<tau>"
  using flip_fresh_fresh by force

lemma no_tyvars_in_kinds[simp]: "atom (a :: tyvar) \<sharp> (k :: \<kappa>)"
  by (induction k rule: \<kappa>.induct) auto

lemma supp_empty_kinds[simp]: "supp (k :: \<kappa>) = {}"
  by (induction k rule: \<kappa>.induct) (auto simp: \<kappa>.supp)

lemma perm_data_name_var[simp]: "((a::var) \<leftrightarrow> b) \<bullet> (T :: data_name) = T"
  using flip_fresh_fresh by force
lemma perm_data_name_tyvar[simp]: "((a::tyvar) \<leftrightarrow> b) \<bullet> (T :: data_name) = T"
  using flip_fresh_fresh by force
lemma perm_ctor_name_var[simp]: "((a::var) \<leftrightarrow> b) \<bullet> (D :: ctor_name) = D"
  using flip_fresh_fresh by force
lemma perm_ctor_name_tyvar[simp]: "((a::tyvar) \<leftrightarrow> b) \<bullet> (D :: ctor_name) = D"
  using flip_fresh_fresh by force

end
