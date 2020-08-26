theory Collecting
  imports ACom Big_Step "HOL-IMP.Complete_Lattice"
begin

notation
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  bot ("\<bottom>") and
  top ("\<top>")

context
  fixes f :: "vname \<Rightarrow> aexp \<Rightarrow> 'a \<Rightarrow> 'a::sup"
  fixes g :: "bexp \<Rightarrow> 'a \<Rightarrow> 'a"
begin
fun Step :: "'a \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"Step S (SKIP {Q}) = (SKIP {S})" |
"Step S (x ::= e {Q}) =
  x ::= e {f x e S}" |
"Step S (C1;; C2) = Step S C1;; Step (post C1) C2" |
"Step S (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
  IF b THEN {g b S} Step P1 C1 ELSE {g (Not b) S} Step P2 C2
  {post C1 \<squnion> post C2}" |
"Step S (C1 OR C2 {P}) =
  Step S C1 OR Step S C2
  {post C1 \<squnion> post C2}" |
"Step S ({I} WHILE b DO {P} C {Q}) =
  {S \<squnion> post C} WHILE b DO {g b I} Step P C {g (Not b) I}"
end


text \<open>Step does not change the underlying command\<close>
lemma strip_Step[simp]: "strip(Step f g S C) = strip C"
by(induct C arbitrary: S) auto


subsubsection "Annotated commands as a complete lattice"

text \<open>We define an order on acom in terms of an order on 'a\<close>
instantiation acom :: (order) order
begin

text \<open>The order is as thus: C1 \<le> C2 once they are on the same base command and all annotations on
C1 \<le> respective annotations on C2\<close>
definition less_eq_acom :: "('a::order)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"C1 \<le> C2 \<longleftrightarrow> strip C1 = strip C2 \<and> (\<forall>p<size(annos C1). anno C1 p \<le> anno C2 p)"

text \<open>We define strict < in terms of our above definition \<le> and equality\<close>
definition less_acom :: "'a acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"less_acom x y = (x \<le> y \<and> \<not> y \<le> x)"

text \<open>We show that our definitions satisfy order axioms\<close>
instance
proof (standard, goal_cases)
  case 1 show ?case by(simp add: less_acom_def)
next
  case 2 thus ?case by(auto simp: less_eq_acom_def)
next
  case 3 thus ?case by(fastforce simp: less_eq_acom_def size_annos)
next
  case 4 thus ?case
    by(fastforce simp: le_antisym less_eq_acom_def size_annos
         eq_acom_iff_strip_anno)
qed

end

text \<open>In terms of list_all2 instead of explicit indexing\<close>
lemma less_eq_acom_annos:
  "C1 \<le> C2 \<longleftrightarrow> strip C1 = strip C2 \<and> list_all2 (\<le>) (annos C1) (annos C2)"
by(auto simp add: less_eq_acom_def anno_def list_all2_conv_all_nth size_annos_same2)

text \<open>Inversion of order when we know the command of the left operand, inferring the command of the
right operand and annotation constraints\<close>

lemma SKIP_le[simp]: "SKIP {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<le> S')"
by (cases c) (auto simp:less_eq_acom_def anno_def)

lemma Assign_le[simp]: "x ::= e {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<le> S')"
by (cases c) (auto simp:less_eq_acom_def anno_def)

lemma Seq_le[simp]: "C1;;C2 \<le> C \<longleftrightarrow> (\<exists>C1' C2'. C = C1';;C2' \<and> C1 \<le> C1' \<and> C2 \<le> C2')"
apply (cases C)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma If_le[simp]: "IF b THEN {p1} C1 ELSE {p2} C2 {S} \<le> C \<longleftrightarrow>
  (\<exists>p1' p2' C1' C2' S'. C = IF b THEN {p1'} C1' ELSE {p2'} C2' {S'} \<and>
     p1 \<le> p1' \<and> p2 \<le> p2' \<and> C1 \<le> C1' \<and> C2 \<le> C2' \<and> S \<le> S')"
apply (cases C)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma Or_le[simp]: "C1 OR C2 {P} \<le> C \<longleftrightarrow>
  (\<exists>C1' C2' P'. C = C1' OR C2' {P'} \<and>
     C1 \<le> C1' \<and> C2 \<le> C2' \<and> P \<le> P')"
apply (cases C)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma While_le[simp]: "{I} WHILE b DO {p} C {P} \<le> W \<longleftrightarrow>
  (\<exists>I' p' C' P'. W = {I'} WHILE b DO {p'} C' {P'} \<and> C \<le> C' \<and> p \<le> p' \<and> I \<le> I' \<and> P \<le> P')"
apply (cases W)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

text \<open>obtaining the last annotation is monotonic\<close>
lemma mono_post: "C \<le> C' \<Longrightarrow> post C \<le> post C'"
using annos_ne[of C']
by(auto simp: post_def less_eq_acom_def last_conv_nth[OF annos_ne] anno_def
     dest: size_annos_same)

text \<open>Inf_acom c M is the infimum among all the annotated commands in M once such an infimum exists\<close>
definition Inf_acom :: "com \<Rightarrow> 'a::complete_lattice acom set \<Rightarrow> 'a acom" where
"Inf_acom c M = annotate (\<lambda>p. INF C\<in>M. anno C p) c"

text \<open>expose the Complete_Lattice theorems conditioned on c (annotated commands form a complete lattice
for each c), once the lemmas are satisfied, where The greatest lower bound for M is Inf_acom c M\<close>
global_interpretation
  Complete_Lattice "{C. strip C = c}" "Inf_acom c" for c
proof (standard, goal_cases)
  case 1 thus ?case
    by(auto simp: Inf_acom_def less_eq_acom_def size_annos intro:INF_lower)
next
  case 2 thus ?case
    by(auto simp: Inf_acom_def less_eq_acom_def size_annos intro:INF_greatest)
next
  case 3 thus ?case by(auto simp: Inf_acom_def)
qed


subsubsection "Collecting semantics"

text \<open>step is Step, partially applied to the assignment and bval semantics of the collecting semantics\<close>
definition "step = Step (\<lambda>x e S. {s(x := aval e s) |s. s \<in> S}) (\<lambda>b S. {s:S. bval b s})"

text \<open>The collecting semantics of a command is its annotation with the smallest set of states that
are invariant under stepping through starting from UNIV\<close>
definition CS :: "com \<Rightarrow> state set acom" where
"CS c = lfp c (step UNIV)"

text \<open>once the assignment and bval semantics are mono, stepping through is mono\<close>
lemma mono2_Step: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S1 S2. S1 \<le> S2 \<Longrightarrow> f x e S1 \<le> f x e S2"
          "!!b S1 S2. S1 \<le> S2 \<Longrightarrow> g b S1 \<le> g b S2"
  shows "C1 \<le> C2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> Step f g S1 C1 \<le> Step f g S2 C2"
proof(induction S1 C1 arbitrary: C2 S2 rule: Step.induct)
  case 1 thus ?case by(auto)
next
  case 2 thus ?case by (auto simp: assms(1))
next
  case 3 thus ?case by(auto simp: mono_post)
next
  case 4 thus ?case
    by(auto simp: subset_iff assms(2))
      (metis mono_post le_supI1 le_supI2)+
next
  case (5 S C1 C2 P CE) thus ?case
    by auto (metis mono_post le_supI1 le_supI2)+
next
  case 6 thus ?case
    by(auto simp: subset_iff assms(2))
      (metis mono_post le_supI1 le_supI2)+
qed

text \<open>and so the same for the step for collecting semantics\<close>
lemma mono2_step: "C1 \<le> C2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> step S1 C1 \<le> step S2 C2"
unfolding step_def by(rule mono2_Step) auto

text \<open>As a corollary, step is mono for fixed S\<close>
lemma mono_step: "mono (step S)"
by(blast intro: monoI mono2_step)

text \<open>stepping does not change the underlying command\<close>
lemma strip_step: "strip(step S C) = strip C"
by (induction C arbitrary: S) (auto simp: step_def)

text \<open>with step being mono, we know that stepping on a fixed S has an lfp\<close>
lemma lfp_cs_unfold: "lfp c (step S) = step S (lfp c (step S))"
apply(rule lfp_unfold[OF _  mono_step])
apply(simp add: strip_step)
done

text \<open>hence CS is a fixpoint with respect to stepping through UNIV\<close>
lemma CS_unfold: "CS c = step UNIV (CS c)"
by (metis CS_def lfp_cs_unfold)

text \<open>CS also has the same underlying c, by closure\<close>
lemma strip_CS[simp]: "strip(CS c) = c"
by(simp add: CS_def index_lfp[simplified])


subsubsection "Relation to big-step semantics"

text \<open>the number of annotations any com admits is nonzero\<close>
lemma asize_nz: "asize(c::com) \<noteq> 0"
by (metis length_0_conv length_annos_annotate annos_ne)

text \<open>The last annotation of the infimum of a set M of annotated commands on c is exactly the
infimum among the annotations. By definition, since infimum is pointwise with respect to the
annotations\<close>
lemma post_Inf_acom:
  "\<forall>C\<in>M. strip C = c \<Longrightarrow> post (Inf_acom c M) = \<Inter>(post ` M)"
apply(subgoal_tac "\<forall>C\<in>M. size(annos C) = asize c")
 apply(simp add: post_anno_asize Inf_acom_def asize_nz neq0_conv[symmetric])
apply(simp add: size_annos)
done

text \<open>Hence similarly for the lfp of f on c\<close>
lemma post_lfp: "post(lfp c f) = (\<Inter>{post C|C. strip C = c \<and> f C \<le> C})"
by(auto simp add: lfp_def post_Inf_acom)

text \<open>our step semantics are correct, so step maps a state in the input state s to satisfying its
last annotation once we know that C is stable under stepping i.e. has (with step S C \<le> C)
(reasoning: step maps each state satisfying annotation to the satisfying the next annotation in
step S C, and by (pointwise) stability, it satisfies that same annotation in C. Then repeat by
stepping through again.)

As for why we use the last annotation, it comes from the big-step semantics that s is the state
before execution of c and t is the state after execution of C\<close>
lemma big_step_post_step:
  "\<lbrakk> (c, s) \<Rightarrow> t;  strip C = c;  s \<in> S;  step S C \<le> C \<rbrakk> \<Longrightarrow> t \<in> post C"
proof(induction arbitrary: C S rule: big_step_induct)
  case Skip thus ?case by(auto simp: strip_eq_SKIP step_def post_def)
next
  case Assign thus ?case
    by(fastforce simp: strip_eq_Assign step_def post_def)
next
  case Seq thus ?case
    by(fastforce simp: strip_eq_Seq step_def post_def last_append annos_ne)
next
  case IfTrue thus ?case apply(auto simp: strip_eq_If step_def post_def)
    by (metis (lifting,full_types) mem_Collect_eq subsetD)
next
  case IfFalse thus ?case apply(auto simp: strip_eq_If step_def post_def)
    by (metis (lifting,full_types) mem_Collect_eq subsetD)
next
  case OrLeft thus ?case apply(auto simp: strip_eq_Or step_def post_def)
    by (metis (lifting,full_types) subsetD)
next
  case OrRight thus ?case apply(auto simp: strip_eq_Or step_def post_def)
    by (metis (lifting,full_types) subsetD)
next
  case (WhileTrue b s1 c' s2 s3)
  from WhileTrue.prems(1) obtain I P C' Q where "C = {I} WHILE b DO {P} C' {Q}" "strip C' = c'"
    by(auto simp: strip_eq_While)
  from WhileTrue.prems(3) \<open>C = _\<close>
  have "step P C' \<le> C'"  "{s \<in> I. bval b s} \<le> P"  "S \<le> I"  "step (post C') C \<le> C"
    by (auto simp: step_def post_def)
  have "step {s \<in> I. bval b s} C' \<le> C'"
    by (rule order_trans[OF mono2_step[OF order_refl \<open>{s \<in> I. bval b s} \<le> P\<close>] \<open>step P C' \<le> C'\<close>])
  have "s1 \<in> {s\<in>I. bval b s}" using \<open>s1 \<in> S\<close> \<open>S \<subseteq> I\<close> \<open>bval b s1\<close> by auto
  note s2_in_post_C' = WhileTrue.IH(1)[OF \<open>strip C' = c'\<close> this \<open>step {s \<in> I. bval b s} C' \<le> C'\<close>]
  from WhileTrue.IH(2)[OF WhileTrue.prems(1) s2_in_post_C' \<open>step (post C') C \<le> C\<close>]
  show ?case .
next
  case (WhileFalse b s1 c') thus ?case
    by (force simp: strip_eq_While step_def post_def)
qed

text \<open>Thus t is also in the the least fixpoint of stepping wrt an S and c\<close>
lemma big_step_lfp: "\<lbrakk> (c,s) \<Rightarrow> t;  s \<in> S \<rbrakk> \<Longrightarrow> t \<in> post(lfp c (step S))"
by(auto simp add: post_lfp intro: big_step_post_step)

text \<open>And so also with UNIV.\<close>
lemma big_step_CS: "(c,s) \<Rightarrow> t \<Longrightarrow> t \<in> post(CS c)"
by(simp add: CS_def big_step_lfp)


end