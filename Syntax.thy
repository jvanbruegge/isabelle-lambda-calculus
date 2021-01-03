theory Syntax
  imports "Nominal2.Nominal2"
begin

atom_decl "var"
atom_decl "tyvar"

nominal_datatype "\<kappa>" =
  Star ("\<star>")
  | KArrow "\<kappa>" "\<kappa>"

nominal_datatype "\<tau>" =
  TyUnit
  | TyVar "tyvar"
  | TyArrow "\<tau>" "\<tau>"  ("_ \<rightarrow> _" 50)
  | TyConApp "\<tau>" "\<tau>"
  | TyForall a::"tyvar" "\<kappa>" t::"\<tau>" binds a in t ("\<forall> _ : _ . _" 50)

nominal_datatype "term" =
   Var "var"
 | App "term" "term"
 | TyApp "term" "\<tau>"
 | Unit
 | Lam x::"var" "\<tau>" e::"term" binds x in e  ("\<lambda> _ : _ . _" 50)
 | TyLam a::"tyvar" "\<kappa>" e::"term" binds a in e ("\<Lambda> _ : _ . _" 50)
 | Let x::"var" "\<tau>" "term" e2::"term" binds x in e2

nominal_datatype "binder" =
  "BVar" "var" "\<tau>"
  | "BTyVar" "tyvar" "\<kappa>"

type_synonym "\<Gamma>" = "binder list"

lemma no_vars_in_kinds[simp]: "atom (x :: var) \<sharp> (k :: \<kappa>)"
  by (induction k rule: \<kappa>.induct) auto
lemma no_vars_in_ty[simp]: "atom (x :: var) \<sharp> (ty :: \<tau>)"
  by (induction ty rule: \<tau>.induct) auto

lemma no_tyvars_in_kinds[simp]: "atom (a :: tyvar) \<sharp> (k :: \<kappa>)"
  by (induction k rule: \<kappa>.induct) auto

lemma supp_empty_kinds[simp]: "supp (k :: \<kappa>) = {}"
  by (induction k rule: \<kappa>.induct) (auto simp: \<kappa>.supp)

end
