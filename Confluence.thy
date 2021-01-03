theory Confluence
  imports Semantics
begin

lemma beta_same[simp]: "\<lbrakk> e1 \<longrightarrow>* e1' ; beta_nf e1 \<rbrakk> \<Longrightarrow> e1 = e1'"
  by (induction e1 e1' rule: Steps.induct) (auto simp: beta_nf_def)

fun path :: "term \<Rightarrow> term list \<Rightarrow> term \<Rightarrow> bool" where
  "path a [] b \<longleftrightarrow> a = b \<or> Step a b"
| "path a (x#xs) b \<longleftrightarrow> Step a x \<and> path x xs b"

lemma path_snoc: "\<lbrakk> path a xs b ; Step b c \<rbrakk> \<Longrightarrow> path a (xs@[b]) c \<or> path a xs c"
  by (induction a xs b arbitrary: c rule: path.induct) auto

lemma Steps_concat: "\<lbrakk> e2 \<longrightarrow>* e3 ; e1 \<longrightarrow>* e2 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"
  apply (induction e2 e3 arbitrary: e1 rule: Steps.induct)
  using Steps.simps by blast+

lemma Steps_path: "a \<longrightarrow>* b \<longleftrightarrow> (\<exists>p. path a p b)"
proof
  assume "a \<longrightarrow>* b"
  then show "\<exists>p. path a p b"
  proof (induction a b rule: Steps.induct)
    case (refl e)
    then have "path e [] e" by simp
    then show ?case by blast
  next
    case (trans e1 e2 e3)
    then obtain xs where "path e1 xs e2" by blast
    then have "path e1 (xs@[e2]) e3 \<or> path e1 xs e3" using trans(2) path_snoc by simp
    then show ?case by blast
  qed
next
  assume "\<exists>p. path a p b"
  then obtain p where "path a p b" by blast
  then show "a \<longrightarrow>* b"
  proof (induction a p b rule: path.induct)
    case (1 a b)
    then show ?case using Steps.intros by auto
  next
    case (2 a x xs b)
    then have a: "a \<longrightarrow>* x" using Steps.intros by auto
    from 2 have b: "x \<longrightarrow>* b" by simp
    show ?case using Steps_concat[OF b a] .
  qed
qed

lemma Steps_fwd_induct[consumes 1, case_names refl trans]:
  assumes "a \<longrightarrow>* b"
    and "\<And>x. P x x" "\<And>x y z. y \<longrightarrow>* z \<Longrightarrow> P y z \<Longrightarrow> Step x y \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from assms(1) obtain p where P: "path a p b" using Steps_path by blast
  then show ?thesis
  proof (induction a p b rule: path.induct)
    case (1 a b)
    then show ?case
    proof (cases "a = b")
      case True
      then show ?thesis using assms(2) by simp
    next
      case False
      then have 1: "Step a b" using 1 by simp
      have 2: "b \<longrightarrow>* b" using Steps.refl by simp
      show ?thesis using assms(3)[OF 2 assms(2) 1] .
    qed
  next
    case (2 a x xs b)
    then have 1: "P x b" by simp
    from 2 have 3: "x \<longrightarrow>* b" using Steps_path by auto
    from 2 have 4: "Step a x" by simp
    show ?case using assms(3)[OF 3 1 4] .
  qed
qed

lemma confluence: "\<lbrakk> a \<longrightarrow>* b ; a \<longrightarrow>* c \<rbrakk> \<Longrightarrow> \<exists>d. b \<longrightarrow>* d \<and> c \<longrightarrow>* d"
  apply (induction a b arbitrary: c rule: Steps_fwd_induct)
  using Steps.refl apply blast
  by (metis Step_deterministic Steps.trans Steps_concat Steps_path path.elims(2))

corollary beta_equivalence: "\<lbrakk> e1 \<longrightarrow>* e1' ; e2 \<longrightarrow>* e2' ; e1 = e2 ; beta_nf e1' ; beta_nf e2' \<rbrakk> \<Longrightarrow> e1' = e2'"
  using beta_same confluence by blast

end
