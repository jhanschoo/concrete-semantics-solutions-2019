theory Chapter5
imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter_0: "iter r 0 x x" |
iter_Suc: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

text \<open>
\section*{Chapter 5}

\exercise
Give a readable, structured proof of the following lemma:
\<close>

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
    and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof -
  have "T x y \<or> T y x" using T by blast
  thus "T x y"
  proof
    assume "T x y"
    thus ?thesis by assumption
  next
    assume "T y x"
    hence "A y x" using TA by blast
    hence "x = y" using A and `A x y` by blast
    thus "T x y" using `T y x` by blast
  qed
qed

text\<open>
Each step should use at most one of the assumptions @{text T}, @{text A}
or @{text TA}.
\endexercise

\exercise
Give a readable, structured proof of the following lemma:
\<close>
lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof -
  have "even (length xs) \<or> odd (length xs)" by simp
  thus ?thesis
  proof
    assume "even (length xs)"
    hence "\<exists> k. k + k = length xs" by arith
    then obtain k where Hk: "k + k = length xs" by auto
    let ?ys = "take k xs"
    let ?zs = "drop k xs"
    have "xs = ?ys @ ?zs" (is ?Heq) by simp
    moreover from Hk have "length ?ys = length ?zs" (is ?Hlen) by auto
    ultimately have "?Heq \<and> ?Hlen" by simp
    thus ?thesis by blast
  next
    assume "odd (length xs)"
    hence "\<exists> k. (k + 1) + k = length xs" by arith
    then obtain k where Hk: "(k + 1) + k = length xs" by auto
    let ?ys = "take (k + 1) xs"
    let ?zs = "drop (k + 1) xs"
    have "xs = ?ys @ ?zs" (is ?Heq) by simp
    moreover from Hk have "length ?ys = length ?zs + 1" (is ?Hlen) by auto
    ultimately have "?Heq \<and> ?Hlen" by simp
    thus ?thesis by blast
  qed
qed

text\<open>
Hint: There are predefined functions @{const take} and {const drop} of type
@{typ "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"} such that @{text"take k [x\<^sub>1,\<dots>] = [x\<^sub>1,\<dots>,x\<^sub>k]"}
and @{text"drop k [x\<^sub>1,\<dots>] = [x\<^bsub>k+1\<^esub>,\<dots>]"}. Let sledgehammer find and apply
the relevant @{const take} and @{const drop} lemmas for you.
\endexercise

\exercise
Give a structured proof by rule inversion:
\<close>
inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof (cases "Suc (Suc n)" rule: ev.cases)
  case ev0
  from a show ?case by assumption
next
  case evSS
  assume "ev n"
  then show ?thesis by assumption
qed

text\<open>
\exercise
Give a structured proof by rule inversions:
\<close>

lemma "\<not> ev(Suc(Suc(Suc 0)))" (is "\<not> ?P")
proof
  assume "?P"
  thus False
  proof (cases "Suc (Suc (Suc 0))")
    case evSS
    thus False by cases
  qed
qed

text\<open>
If there are no cases to be proved you can close
a proof immediateley with \isacom{qed}.
\endexercise

\exercise
Recall predicate @{const star} from Section 4.5 and @{const iter}
from Exercise~\ref{exe:iter}.
\<close>

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induct rule: iter.induct)
  case (iter_0 x)
  show ?case by (simp add: refl)
next
  case (iter_Suc x y n z)
  thus ?case by (simp add: step)
qed

text\<open>
Prove this lemma in a structured style, do not just sledgehammer each case of the
required induction.
\endexercise

\exercise
Define a recursive function
\<close>

fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" |
  "elems (x # xs) = {x} \<union> elems xs"

text\<open> that collects all elements of a list into a set. Prove \<close>

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induct xs)
  case Nil
  hence False by simp
  thus ?case by simp
next
  case (Cons a xs)
  hence HxUn: "x \<in> {a} \<union> elems xs" by simp
  consider (xa) "x \<in> {a}" | (nxa) "x \<notin> {a}" by blast
  thus ?case
  proof cases
    case xa
    hence "x = a" ..
    hence "a # xs = x # xs" by simp
    also have "\<dots> = [] @ x # xs" by simp
    finally have "a # xs = [] @ x # xs" by simp
    moreover have "x \<notin> {}" by simp
    hence "x \<notin> elems []" by simp
    ultimately show ?thesis by blast
  next
    case nxa
    from HxUn
    show ?thesis
    proof
      assume "x \<in> {a}"
      thus ?thesis using nxa by simp
    next
      assume "x \<in> elems xs"
      then obtain ys zs where "xs = ys @ x # zs" and "x \<notin> elems ys" using Cons.hyps by blast
      hence "a # xs = (a # ys) @ x # zs" and "x \<notin> elems ys" by auto
      hence "a # xs = (a # ys) @ x # zs" and "x \<notin> elems (a # ys)" using nxa by auto
      thus ?thesis by blast
    qed
  qed
qed

text\<open>
\endexercise

\exercise
Extend Exercise~\ref{exe:cfg} with a function that checks if some
\mbox{@{text "alpha list"}} is a balanced
string of parentheses. More precisely, define a recursive function \<close>

datatype alpha = alphaa | alphab

inductive S :: "alpha list \<Rightarrow> bool" where
S_\<epsilon>: "S []" |
S_aSb: "S w \<Longrightarrow> S (alphaa # w @ [alphab])" |
S_SS: "\<lbrakk> S v; S w \<rbrakk> \<Longrightarrow> S (v @ w)"

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True" |
  "balanced (Suc _) [] = False" | (* too many a's *)
  "balanced n (alphaa # as) = balanced (Suc n) as" |
  "balanced 0 (alphab # as) = False" | (* too many b's *)
  "balanced (Suc n) (alphab # as) = balanced n as"

text\<open> such that @{term"balanced n w"}
is true iff (informally) @{text"a\<^sup>n @ w \<in> S"}. Formally, prove \<close>

lemma balanced_r: "balanced n as \<Longrightarrow> balanced (Suc n) (as @ [alphab])"
proof (induction n as rule: balanced.induct)
  case 1
  thus ?case by simp
next
  case (2 uu)
  thus ?case by simp
next
  case (3 n as)
  from 3(2) have "balanced (Suc n) as" by simp
  thus ?case using 3(1) by simp
next
  case (4 as)
  then show ?case by simp
next
  case (5 n as)
  from 5(2) have "balanced n as" by simp
  thus ?case using 5(1) by simp
qed

lemma balanced_app: "\<lbrakk>balanced m as; balanced n bs\<rbrakk> \<Longrightarrow> balanced (m + n) (as @ bs)"
proof (induct m as arbitrary: n bs rule: balanced.induct)
  case 1
  then show ?case by simp
next
  case (2 uu)
  then show ?case by simp
next
  case (3 nn as)
  from 3(2) have "balanced (Suc nn) as" by simp
  with 3(1, 3) have "balanced (Suc nn + n) (as @ bs)" by simp
  hence "balanced (Suc (nn + n)) (as @ bs)" by simp
  thus ?case by simp
next
  case (4 as)
  then show ?case by simp
next
  case (5 nn as)
  from 5(2) have "balanced nn as" by simp
  with 5(1, 3) have "balanced (nn + n) (as @ bs)" by simp
  hence "balanced (Suc (nn + n)) (alphab # as @ bs)" by simp
  thus ?case by simp
qed

lemma S_ends: "S w \<Longrightarrow> w = [] \<or> (\<exists> v. w = alphaa # v @ [alphab])"
proof (induct w rule: S.induct)
  case S_\<epsilon>
  have "[] = []" by simp
  thus ?case by blast
next
  case (S_aSb w)
  have "alphaa # w @ [alphab] = alphaa # w @ [alphab]" by simp
  thus ?case by blast
next
  case (S_SS v w)
  from S_SS(2) show ?case
  proof
    assume Hv: "v = []"
    from S_SS(4) show ?thesis
    proof
      assume "w = []"
      with Hv have "v @ w = []" by simp
      thus ?thesis by blast
    next
      assume "\<exists>u. w = alphaa # u @ [alphab]"
      then obtain u where "w = alphaa # u @ [alphab]" ..
      with Hv have "v @ w = alphaa # u @ [alphab]" by simp
      thus ?thesis by blast
    qed
  next
    assume "\<exists>u. v = alphaa # u @ [alphab]"
    then obtain n where Hv: "v = alphaa # n @ [alphab]" ..
    from S_SS(4) show ?thesis
    proof
      assume "w = []"
      with Hv have "v @ w = alphaa # n @ [alphab]" by simp
      thus ?thesis by blast
    next
      assume "\<exists>u. w = alphaa # u @ [alphab]"
      then obtain m where "w = alphaa # m @ [alphab]" ..
      with Hv have "v @ w = alphaa # n @ [alphab] @ alphaa # m @ [alphab]" by simp
      hence "v @ w = alphaa # (n @ [alphab] @ alphaa # m) @ [alphab]" by simp
      thus ?thesis by blast
    qed
  qed
qed

lemma S_replicate: "\<lbrakk>S (alphaa # v); v @ w = replicate n alphaa @ x\<rbrakk> \<Longrightarrow> \<exists> u. v = replicate n alphaa @ u"
proof -
  assume Hvw: "v @ w = replicate n alphaa @ x"
  assume Sav: "S (alphaa # v)"
  hence "\<exists> vv. alphaa # v = alphaa # vv @ [alphab]"
  proof -
    assume "S (alphaa # v)"
    with S_ends have "alphaa # v = [] \<or> (\<exists> vv. alphaa # v = alphaa # vv @ [alphab])" by auto
    thus "\<exists>vv. alphaa # v = alphaa # vv @ [alphab]"
    proof
      assume "alphaa # v = []"
      thus ?thesis by simp
    next
      assume "\<exists>vv. alphaa # v = alphaa # vv @ [alphab]"
      thus ?thesis by simp
    qed
  qed
  then obtain vv where "alphaa # v = alphaa # vv @ [alphab]" ..
  hence Hv: "v = vv @ [alphab]" by simp
  hence Hvvw: "vv @ [alphab] @ w = replicate n alphaa @ x" using Hvw by simp
  hence "\<exists> xx. vv @ [alphab] = replicate n alphaa @ xx"
  proof (induct n arbitrary: x)
    case 0
    have "vv @ [alphab] = replicate 0 alphaa @ vv @ [alphab]" by simp
    thus ?case by simp
  next
    case (Suc n)
    from Suc(2) have Suc2s: "vv @ [alphab] @ w = replicate n alphaa @ alphaa # x" by (simp add: replicate_app_Cons_same)
    hence "\<exists>xx. vv @ [alphab] = replicate n alphaa @ xx" using Suc(1) by simp
    then obtain xx where Hxx1: "vv @ [alphab] = replicate n alphaa @ xx" ..
    hence "\<exists> xl. vv @ [alphab] = replicate n alphaa @ xl @ [alphab]"
      by (metis alpha.distinct(1) append_butlast_last_id empty_replicate last_append last_replicate last_snoc self_append_conv2)
    then obtain xl where Hvvb: "vv @ [alphab] = replicate n alphaa @ xl @ [alphab]" ..
    hence Hxl1: "vv = replicate n alphaa @ xl" by simp
    with Suc2s have "replicate n alphaa @ xl @ [alphab] @ w = replicate n alphaa @ alphaa # x" by simp
    hence Hxx: "xl @ [alphab] @ w = alphaa # x" by simp
    hence "\<exists> xlr. xl = alphaa # xlr"
      by (metis alpha.distinct(1) append_eq_Cons_conv list.sel(1))
    then obtain xlr where "xl = alphaa # xlr" ..
    with Hvvb have "vv @ [alphab] = replicate n alphaa @ alphaa # xlr @ [alphab]" by simp
    hence "vv @ [alphab] = replicate (Suc n) alphaa @ xlr @ [alphab]" by (simp add: replicate_app_Cons_same)
    then show ?case by blast
  qed
  thus ?thesis using Hv by simp
qed

corollary "balanced n w \<longleftrightarrow> S (replicate n alphaa @ w)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  thus ?Q
  proof (induct n w rule: balanced.induct)
    case 1 show ?case by (auto intro: S.S_\<epsilon>)
  next case (2 uu) thus ?case by simp
  next
    case (3 n as)
    moreover from this have "balanced (Suc n) as" by simp
    ultimately have "S (replicate (Suc n) alphaa @ as)" by simp
    hence "S ((replicate n alphaa @ [alphaa]) @ as)" by (simp add: replicate_append_same)
    thus ?case by auto
  next case (4 as) thus ?case by simp
  next
    case (5 n as)
    moreover from this have "balanced n as" by simp
    ultimately have "S (replicate n alphaa @ as)" by simp
    then show ?case
    proof (induct "replicate n alphaa @ as" arbitrary: n as rule: S.induct)
      case S_\<epsilon>
      from S_\<epsilon> have Hn: "replicate n alphaa = []" by simp
      from S_\<epsilon> have Has: "as = []" by simp
      from Hn have Hl: "replicate (Suc n) alphaa = [alphaa]" by simp
      from S.S_\<epsilon> have "S []" by simp
      with S.S_aSb have "S (alphaa # [] @ [alphab])" by blast
      with Hl Has show ?case by auto
    next
      case (S_aSb w)
      then show ?case
      proof (cases "rev as")
        case Nil
        hence "alphaa # w @ [alphab] = replicate n alphaa @ []" using S_aSb(3) by simp
        thus ?thesis
          by (metis Nil_is_append_conv alpha.distinct(1) append_Nil2 empty_replicate last.simps last_replicate last_snoc list.discI)
      next
        case (Cons a al)
        hence Has: "as = rev al @ [a]" by simp
        hence Ha: "a = alphab" using S_aSb(3) by auto
        from S_aSb(3) Has Ha have Haw: "alphaa # w = replicate n alphaa @ rev al" by auto
        have "S (replicate (Suc n) alphaa @ alphab # rev al @ [a])"
        proof (cases n)
          case 0
          with Haw have "alphaa # w @ [alphab] = rev al @ [alphab]" by simp
          with S_aSb(1) S.S_aSb have "S (rev al @ [alphab])" by metis
          moreover 
          from S.S_\<epsilon> have "S []" by simp
          with S.S_aSb have "S (alphaa # [] @ [alphab])" by blast
          hence "S ([alphaa, alphab])" by simp
          ultimately have "S ([alphaa, alphab] @ rev al @ [alphab])" using S.S_SS by blast
          hence "S ([alphaa] @ alphab # rev al @ [alphab])" by auto
          with 0 Ha show ?thesis by auto
        next
          case (Suc m)
          with Haw have Hw: "w = replicate m alphaa @ rev al" by simp
          with S_aSb(2) have "S (replicate (Suc m) alphaa @ alphab # rev al)" by blast
          with S.S_aSb have "S (alphaa # (replicate (Suc m) alphaa @ alphab # rev al) @ [alphab])" by blast
          hence "S (replicate (Suc (Suc m)) alphaa @ alphab # rev al @ [alphab])" by auto
          thus ?thesis using Suc Ha by simp
        qed
        thus ?thesis using Has by simp
      qed
    next
      case (S_SS v w)
      from \<open>S v\<close> have "v = [] \<or> (\<exists> k. v = alphaa # k @ [alphab])" using S_ends by simp
      then show ?case
      proof
        assume "v = []"
        with S_SS(5) have "w = replicate n alphaa @ as" by simp
        with S_SS(4) show ?thesis by simp
      next
        assume "\<exists>k. v = alphaa # k @ [alphab]"
        then obtain k where Hk: "v = alphaa # k @ [alphab]" ..
        show ?thesis
        proof (cases n)
          case 0
          with S_SS(5) have "v @ w = as" by simp
          with S.S_SS S_SS(1,3) have "S as" by blast
          moreover
          from S.S_\<epsilon> have "S []" by simp
          with S.S_aSb have "S (alphaa # [] @ [alphab])" by blast
          hence "S ([alphaa] @ [alphab])" by auto
          ultimately have "S (([alphaa] @ [alphab]) @ as)" using S.S_SS by blast
          thus ?thesis using 0 by auto
        next
          case (Suc m)
          have "S (alphaa # k @ [alphab])" using \<open>S v\<close> and Hk by simp
          moreover
          from this Suc S_SS(5) have "v @ w = alphaa # replicate m alphaa @ as" by simp
          with Hk have "k @ [alphab] @ w = replicate m alphaa @ as" by simp
          ultimately have "\<exists> u. k @ [alphab] = replicate m alphaa @ u" using S_replicate by simp
          then obtain u where "k @ [alphab] = replicate m alphaa @ u" ..
          hence "v = alphaa # replicate m alphaa @ u" using Hk by simp
          hence Hv: "v = replicate n alphaa @ u" using Suc by simp
          hence Svv: "S (replicate (Suc n) alphaa @ alphab # u)" using S_SS(2) by simp
          from Hv S_SS(5) have Has: "as = u @ w" by simp
          from Svv S_SS(3) S.S_SS have "S ((replicate (Suc n) alphaa @ alphab # u) @ w)" by blast
          with Has show ?thesis by auto
        qed
      qed
    qed
  qed
next
  assume ?Q
  thus ?P
  proof (induct "replicate n alphaa @ w" arbitrary: n w rule: S.induct)
    case S_\<epsilon>
    hence "replicate n alphaa = []" by simp
    hence "n = 0" by simp
    moreover from S_\<epsilon> have "w = []" by simp
    ultimately show ?case by simp
  next
    case (S_aSb ww)
    then show ?case
    proof (cases n)
      case 0
      with S_aSb have Hw: "w = alphaa # ww @ [alphab]" by simp
      from S_aSb(2) have "balanced 0 ww" by auto
      hence "balanced (Suc 0) (ww @ [alphab])" using balanced_r by simp
      hence "balanced 0 (alphaa # ww @ [alphab])" by simp
      with 0 Hw show ?thesis by simp
    next
      case (Suc m)
      with S_aSb(3) have Hwwb: "ww @ [alphab] = replicate m alphaa @ w" by simp
      hence "\<exists> wl. ww @ [alphab] = replicate m alphaa @ wl @ [alphab]"
        by (metis alpha.distinct(1) append_butlast_last_id empty_replicate last_append last_replicate last_snoc self_append_conv2)
      then obtain wl where Hww: "ww = replicate m alphaa @ wl" by auto
      with S_aSb(2) have Bwl: "balanced m wl" by blast
      from Hwwb Hww have Hw: "w = wl @ [alphab]" by simp
      from Bwl balanced_r have "balanced (Suc m) (wl @ [alphab])" by simp
      thus ?thesis using Hw Suc by simp
    qed
  next
    case (S_SS vv ww)
    from S_SS(1) S_ends have "vv = [] \<or> (\<exists>vvv. vv = alphaa # vvv @ [alphab])" by simp
    thus ?case
    proof
      assume "vv = []"
      with S_SS(5) have "ww = replicate n alphaa @ w" by simp
      with S_SS(4) show ?thesis by simp
    next
      assume "\<exists>vvv. vv = alphaa # vvv @ [alphab]"
      then obtain vvv where Hvv: "vv = alphaa # vvv @ [alphab]" ..
      hence Svv: "S (alphaa # vvv @ [alphab])" using S_SS(1) by simp
      show ?thesis
      proof (cases n)
        case 0
        with S_SS(5) have Hw: "w = vv @ ww" by simp
        from S_SS(2) have Hvv: "balanced 0 vv" by simp
        from S_SS(4) have Hww: "balanced 0 ww" by simp
        from Hvv Hww balanced_app Hw have "balanced (0 + 0) w" by blast
        with 0 show ?thesis by simp
      next
        case (Suc m)
        hence H: "vvv @ [alphab] @ ww = replicate m alphaa @ w" using Hvv S_SS(5) by auto
        hence "\<exists> u. vvv @ [alphab] = replicate m alphaa @ u" using Svv S_replicate by auto
        then obtain u where Hu: "vvv @ [alphab] = replicate m alphaa @ u" ..
        hence "vv = replicate n alphaa @ u" using Hvv Suc by auto
        with S_SS(2) have Hbu: "balanced n u" by simp
        from H have H': "(vvv @ [alphab]) @ ww = replicate m alphaa @ w" by simp
        from Hu H' have "replicate m alphaa @ u @ ww = replicate m alphaa @ w" by auto 
        from Hu H' have Hw: "u @ ww = w" by auto
        from S_SS(3, 4) have Hbww: "balanced 0 ww" by simp
        hence "balanced (n + 0) (u @ ww)" using Hbu balanced_app by blast
        thus ?thesis using Hw by auto
      qed
    qed
  qed
qed

text\<open> where @{const replicate} @{text"::"} @{typ"nat \<Rightarrow> 'a \<Rightarrow> 'a list"} is predefined
and @{term"replicate n x"} yields the list @{text"[x, \<dots>, x]"} of length @{text n}.
\<close>

end

