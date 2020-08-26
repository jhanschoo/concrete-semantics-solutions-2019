(* Author: Tobias Nipkow *)

subsection "Computable Abstract Interpretation"

theory Abs_Int1
imports Abs_State
begin

text\<open>Abstract interpretation over type \<open>st\<close> instead of functions.\<close>

context Gamma_semilattice
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
  "aval' (N i) S = num' i" |
  "aval' (V x) S = fun S x" |
  "aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_correct: "s \<in> \<gamma>\<^sub>s S \<Longrightarrow> aval a s \<in> \<gamma>(aval' a S)"
  by (induction a) (auto simp: gamma_num' gamma_plus' \<gamma>_st_def)

fun bval' :: "bexp \<Rightarrow> 'av st \<Rightarrow> bool option" where
  "bval' (Bc v) _ = Some v" |
  "bval' (Not b) S = (case bval' b S of None \<Rightarrow> None | Some v' \<Rightarrow> Some (\<not>v'))" |
  "bval' (And b\<^sub>1 b\<^sub>2) S = (case (bval' b\<^sub>1 S, bval' b\<^sub>2 S) of
    (Some False, _) \<Rightarrow> Some False |
    (_, Some False) \<Rightarrow> Some False |
    (None, _) \<Rightarrow> None |
    (_, None) \<Rightarrow> None |
    (Some True, Some True) \<Rightarrow> Some True)" |
  "bval' (Less a\<^sub>1 a\<^sub>2) S = less' (aval' a\<^sub>1 S) (aval' a\<^sub>2 S)"

lemma bval'_correct: "s \<in> \<gamma>\<^sub>s S \<Longrightarrow> bval' b S = None \<or> bval' b S = Some (bval b s)"
  by (induct b) (auto simp: gamma_less' aval'_correct split: bool.split_asm)

lemma gamma_Step_subcomm: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S. f1 x e (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (f2 x e S)"
          "!!b S. g1 b (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (g2 b S)"
  shows "Step f1 g1 (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (Step f2 g2 S C)"
proof(induction C arbitrary: S)
qed (auto simp: assms intro!: mono_gamma_o sup_ge1 sup_ge2)

lemma in_gamma_update: "\<lbrakk> s \<in> \<gamma>\<^sub>s S; i \<in> \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) \<in> \<gamma>\<^sub>s(update S x a)"
by(simp add: \<gamma>_st_def)

end


locale Abs_Int = Gamma_semilattice where \<gamma>=\<gamma>
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
begin

definition "step' = Step
  (\<lambda>x e S. case S of None \<Rightarrow> None | Some S' \<Rightarrow> Some(update S' x (aval' e S')))
  (\<lambda>b S. case S of None \<Rightarrow> None |
    Some S' \<Rightarrow> (case bval' b S' of Some False \<Rightarrow> None | _ \<Rightarrow> Some S'))"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"


lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(simp add: step'_def)


text\<open>Correctness:\<close>

lemma step_step': "step (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' S C)"
unfolding step_def step'_def
proof (rule gamma_Step_subcomm, auto simp: intro!: aval'_correct in_gamma_update split: option.splits bool.splits)
  fix b s S
  assume "s \<in> \<gamma>\<^sub>s S"
  then have "bval' b S = None \<or> bval' b S = Some (bval b s)" by (simp add: bval'_correct)
  moreover assume "bval' b S = Some False"
  ultimately have "\<not>bval b s" by auto
  moreover assume "bval b s"
  ultimately show False by auto
qed

lemma AI_correct: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^sub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "pfp (step' \<top>) (bot c) = Some C"
  have pfp': "step' \<top> C \<le> C" by(rule pfp_pfp[OF 1])
  have 2: "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c C"  \<comment> \<open>transfer the pfp'\<close>
  proof(rule order_trans)
    show "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' \<top> C)" by(rule step_step')
    show "... \<le> \<gamma>\<^sub>c C" by (metis mono_gamma_c[OF pfp'])
  qed
  have 3: "strip (\<gamma>\<^sub>c C) = c" by(simp add: strip_pfp[OF _ 1] step'_def)
  have "lfp c (step (\<gamma>\<^sub>o \<top>)) \<le> \<gamma>\<^sub>c C"
    by(rule lfp_lowerbound[simplified,where f="step (\<gamma>\<^sub>o \<top>)", OF 3 2])
  thus "lfp c (step UNIV) \<le> \<gamma>\<^sub>c C" by simp
qed

end


end
