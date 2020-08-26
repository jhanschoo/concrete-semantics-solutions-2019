theory Short_Theory_11_7
  imports "HOL-IMP.Denotational" "HOL-IMP.Vars"
begin

fun Dep :: "com \<Rightarrow> (vname * vname) set" where
  "Dep SKIP = Id" |
  "Dep (x::=a) = {(u,v). if v = x then u \<in> vars a else u = v}" |
  "Dep (c1;;c2) = Dep c1 O Dep c2" |
  "Dep (IF b THEN c1 ELSE c2) = Dep c1 \<union> Dep c2 \<union> vars b \<times> (lvars c1 \<union> lvars c2)" |
  "Dep (WHILE b DO c) = lfp (\<lambda>R. Id \<union> vars b \<times> lvars c \<union> Dep c O R)"

abbreviation Deps :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
  "Deps c X \<equiv> (\<Union> x\<in>X. {y. (y, x) \<in> Dep c})"

lemma nlvars_Dep: "\<lbrakk>lvars c \<inter> X = {}; x \<in> X; (y, x) \<in> Dep c\<rbrakk> \<Longrightarrow> y = x"
proof (induct c arbitrary: x y)
  case (Assign x1 x2)
  from Assign(1) have "x1 \<notin> X" by simp
  with Assign(2) have "x \<noteq> x1" by auto
  with Assign(3) show ?case by simp
next
  case (Seq c1 c2)
  from Seq(3) have Hv: "lvars c1 \<inter> X = {}" "lvars c2 \<inter> X = {}" by auto
  from Seq(5) obtain x' where Hd: "(y, x') \<in> Dep c1" "(x', x) \<in> Dep c2" by auto
  from Seq(2) [OF Hv(2) Seq(4) Hd(2)] have "x' = x" .
  moreover from this Seq(4) have "x' \<in> X" by simp
  from Seq(1) [OF Hv(1) this Hd(1)] have "y = x'" .
  ultimately show ?case by simp
next
  case (If b c1 c2)
  from If(3) have Hv: "lvars c1 \<inter> X = {}" "lvars c2 \<inter> X = {}" by auto
  from If(5) consider (Hc1) "(y, x) \<in> Dep c1" | (Hc2) "(y, x) \<in> Dep c2" | (Hb) "(y, x) \<in> vars b \<times> (lvars c1 \<union> lvars c2)" by auto
  then show ?case
  proof cases
    case Hc1
    from If(1) [OF Hv(1) If(4) this] show ?thesis .
  next
    case Hc2
    from If(2) [OF Hv(2) If(4) this] show ?thesis .
  next
    case Hb
    with If(4) have "x \<in> lvars (IF b THEN c1 ELSE c2) \<inter> X" by simp
    with If(3) show ?thesis by simp
  qed
next
  case (While b c)
  let ?f = "\<lambda>R. Id \<union> vars b \<times> lvars c \<union> Dep c O R"
  let ?GX = "{(y, x)|y x. x \<in> X \<longrightarrow> y = x}"
  from While(2) have lcXv: "lvars c \<inter> X = {}" by simp
  have "Id \<subseteq> ?GX" by auto
  moreover from lcXv have "vars b \<times> lvars c \<subseteq> ?GX" by auto
  moreover have "Dep c O ?GX \<subseteq> ?GX"
  proof
    fix p
    assume pin: "p \<in> Dep c O ?GX"
    then obtain x y where xy: "p = (y, x)" by auto
    show "p \<in> ?GX"
    proof (cases "x \<in> X")
      case True
      from pin xy obtain x' where xx'y: "(y, x') \<in> Dep c" "(x', x) \<in> ?GX" by auto
      from True xx'y(2) have "x' = x" by simp
      moreover from True this have "x' \<in> X" by simp
      from While(1) [OF lcXv this xx'y(1)] have "y = x'" .
      ultimately have "y = x" by simp
      with xy show ?thesis by simp
    next
      case False
      with xy show ?thesis by simp
    qed
  qed
  ultimately have "?f ?GX \<subseteq> ?GX" by simp
  then have "lfp ?f \<subseteq> ?GX" by (auto intro!: lfp_lowerbound)
  with While(4) have "(y, x) \<in> ?GX" by auto
  with While(3) show ?case by simp
qed simp

lemma nlvars_Dep_str: "\<lbrakk>lvars c \<inter> X = {}; x \<in> X\<rbrakk> \<Longrightarrow> (x, x) \<in> Dep c"
proof (induct c arbitrary: x)
  case (Assign x1 x2)
  from Assign(1, 2) have "x \<noteq> x1" by auto
  then show ?case by simp
next
  case (While b c)
  from While(2) have lcXv: "lvars c \<inter> X = {}" by simp
  from While(1) [OF this While(3)] have "(x, x) \<in> Dep c" .
  moreover let ?f = "\<lambda>R. Id \<union> vars b \<times> lvars c \<union> Dep c O R"
  have "mono ?f" unfolding mono_def by auto
  from lfp_fixpoint [OF this] have "?f (lfp ?f) = lfp ?f" .
  ultimately show ?case by auto
qed auto

lemma nlvars_Deps_X: "lvars c \<inter> X = {} \<Longrightarrow> Deps c X \<subseteq> X"
proof
  fix y
  assume assm: "lvars c \<inter> X = {}" "y \<in> Deps c X"
  from this(2) obtain x where Hx: "(y, x) \<in> Dep c" "x \<in> X" by auto
  from nlvars_Dep [OF assm(1) Hx(2) Hx(1)] have "y = x" .
  with Hx(2) show "y \<in> X" by simp
qed

lemma nlvars_X_Deps: "lvars c \<inter> X = {} \<Longrightarrow> X \<subseteq> Deps c X"
  by (auto simp add: nlvars_Dep_str)

lemma nlvars_Deps: "lvars c \<inter> X = {} \<Longrightarrow> Deps c X = X"
  by (intro equalityI) (simp add: nlvars_Deps_X nlvars_X_Deps)+

lemma nlvars_big_step: "\<lbrakk>(c, s) \<Rightarrow> s'; lvars c \<inter> X = {}\<rbrakk> \<Longrightarrow> s = s' on X"
proof (induct rule: big_step_induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(5) have "lvars c\<^sub>1 \<inter> X = {}" "lvars c\<^sub>2 \<inter> X = {}" by auto
  with Seq show ?case by auto
qed auto

lemma "\<lbrakk>(c, s) \<Rightarrow> s'; (c, t) \<Rightarrow> t'; s = t on Deps c X\<rbrakk> \<Longrightarrow> s' = t' on X"
proof (induct arbitrary: t t' X rule: big_step_induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(5) obtain ti where Hti: "(c\<^sub>1, t) \<Rightarrow> ti" "(c\<^sub>2, ti) \<Rightarrow> t'" by auto
  from Seq(6) have "s\<^sub>1 = t on Deps c\<^sub>1 (Deps c\<^sub>2 X)" by auto
  from Seq(2) [OF Hti(1) this] have "s\<^sub>2 = ti on Deps c\<^sub>2 X" .
  from Seq(4) [OF Hti(2) this] show ?case .
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  let ?i = "IF b THEN c\<^sub>1 ELSE c\<^sub>2"
  show ?case
  proof (cases "lvars ?i \<inter> X = {}")
    case True
    from nlvars_Deps [OF this] IfTrue(5) have "s = t on X" by simp
    moreover from True have "lvars c\<^sub>1 \<inter> X = {}" by auto
    from nlvars_big_step [OF IfTrue(2) this] have "s = s' on X" .
    moreover from nlvars_big_step [OF IfTrue(4) True] have "t = t' on X" .
    ultimately show ?thesis by simp
  next
    case False
    with IfTrue(5) have Heq: "s = t on vars b" "s = t on Deps c\<^sub>1 X" by auto
    from bval_eq_if_eq_on_vars [OF Heq(1)] IfTrue(1) have "bval b t" by simp
    with IfTrue(4) have "(c\<^sub>1, t) \<Rightarrow> t'" by auto
    from IfTrue(3) [OF this Heq(2)] show ?thesis .
  qed
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  let ?i = "IF b THEN c\<^sub>1 ELSE c\<^sub>2"
  show ?case
  proof (cases "lvars ?i \<inter> X = {}")
    case True
    from nlvars_Deps [OF this] IfFalse(5) have "s = t on X" by simp
    moreover from True have "lvars c\<^sub>2 \<inter> X = {}" by auto
    from nlvars_big_step [OF IfFalse(2) this] have "s = s' on X" .
    moreover from nlvars_big_step [OF IfFalse(4) True] have "t = t' on X" .
    ultimately show ?thesis by simp
  next
    case False
    with IfFalse(5) have Heq: "s = t on vars b" "s = t on Deps c\<^sub>2 X" by auto
    from bval_eq_if_eq_on_vars [OF Heq(1)] IfFalse(1) have "\<not>bval b t" by simp
    with IfFalse(4) have "(c\<^sub>2, t) \<Rightarrow> t'" by auto
    from IfFalse(3) [OF this Heq(2)] show ?thesis .
  qed
next
  case (WhileFalse b s c)
  let ?f = "\<lambda>R. Id \<union> vars b \<times> lvars c \<union> Dep c O R"
  let ?w = "WHILE b DO c"
  have monof: "mono ?f" unfolding mono_def by auto
  from lfp_fixpoint [OF this] have fpf: "?f (lfp ?f) = lfp ?f" .
  show ?case
  proof (cases "lvars ?w \<inter> X = {}")
    case True
    from nlvars_Deps [OF this] WhileFalse(3) have "s = t on X" by simp
    moreover from nlvars_big_step [OF WhileFalse(2) True] have "t = t' on X" .
    ultimately show "s = t' on X" by simp
  next
    case False
    then have "vars b \<subseteq> (\<Union> x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps ?w X" by simp
    finally have "vars b \<subseteq> Deps ?w X" .
    with WhileFalse(3) have Heq1: "s = t on vars b" by auto
    from bval_eq_if_eq_on_vars [OF Heq1] WhileFalse(1) have "\<not>bval b t" by simp
    with WhileFalse(2) have Htt': "t' = t" by auto
    from False have "X \<subseteq> (\<Union>x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps ?w X" by simp
    finally have Heq2: "X \<subseteq> Deps ?w X" .
    with WhileFalse(3) Htt' show ?thesis by auto
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?f = "\<lambda>R. Id \<union> vars b \<times> lvars c \<union> Dep c O R"
  let ?w = "WHILE b DO c"
  have monof: "mono ?f" unfolding mono_def by auto
  from lfp_fixpoint [OF this] have fpf: "?f (lfp ?f) = lfp ?f" .
  show ?case
  proof (cases "lvars ?w \<inter> X = {}")
    case True
    from nlvars_Deps [OF True] WhileTrue(7) have "s\<^sub>1 = t on X" by simp
    moreover from True have "lvars c \<inter> X = {}" by simp
    from nlvars_big_step [OF WhileTrue(2) this] have "s\<^sub>1 = s\<^sub>2 on X" .
    moreover from nlvars_big_step [OF WhileTrue(4) True] have "s\<^sub>2 = s\<^sub>3 on X" .
    moreover from nlvars_big_step [OF WhileTrue(6) True] have "t = t' on X" .
    ultimately show ?thesis by simp
  next
    case False
    then have "vars b \<subseteq> (\<Union> x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps ?w X" by simp
    finally have "vars b \<subseteq> Deps ?w X" .
    with WhileTrue(7) have Heq1: "s\<^sub>1 = t on vars b" by auto
    from bval_eq_if_eq_on_vars [OF Heq1] WhileTrue(1) have "bval b t" by simp
    with WhileTrue(6) obtain ti where Htw: "(c, t) \<Rightarrow> ti" "(?w, ti) \<Rightarrow> t'" by auto
    have "Deps c (Deps ?w X) \<subseteq> Deps ?w X" using lfp_fixpoint [OF monof] by auto
    with WhileTrue(7) have "s\<^sub>1 = t on Deps c (Deps ?w X)" by blast
    from WhileTrue(3) [OF Htw(1) this] have "s\<^sub>2 = ti on Deps ?w X" .
    from WhileTrue(5) [OF Htw(2) this] show ?thesis .
  qed
qed auto

lemma "\<exists> c s s' t X. (c, s) \<Rightarrow> s' \<and> s = t on Deps c X \<and> (\<nexists>t'. (c, t) \<Rightarrow> t')"
proof -
  let ?b = "Less (N 0) (V ''x'')"
  let ?c = "SKIP"
  let ?w = "WHILE ?b DO ?c"
  let ?s = "<> :: vname \<Rightarrow> val"
  let ?t = "<''x'' := 1> :: vname \<Rightarrow> val"
  have H1: "(?w, ?s) \<Rightarrow> ?s" unfolding null_state_def by auto
  have H2: "?s = ?t on Deps ?w {}" by simp
  have Hbt: "bval ?b ?t" by simp
  have H3: "\<nexists>t'. (?w, ?t) \<Rightarrow> t'"
  proof
    assume "\<exists>t'. (?w, ?t) \<Rightarrow> t'"
    then obtain t' where "(?w, ?t) \<Rightarrow> t'" by auto
    then show "False"
      using Hbt by (induct "?w" "?t" t' rule: big_step_induct) auto
  qed
  from H1 H2 H3 show ?thesis by blast
qed

