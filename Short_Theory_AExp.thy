theory Short_Theory_AExp
  imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) _ = n" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
  "aval (Times a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s * aval a\<^sub>2 s"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N (i\<^sub>1 + i\<^sub>2)" |
  "plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i = 0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "times (N i\<^sub>1) (N i\<^sub>2) = N (i\<^sub>1 * i\<^sub>2)" |
  "times (N i) a = (if i = 1 then a else Times (N i) a)" |
  "times a (N i) = (if i = 1 then a else Times a (N i))" |
  "times a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
    (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
      (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N (n\<^sub>1 + n\<^sub>2) |
      (b\<^sub>1, b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)" |
  "asimp_const (Times a\<^sub>1 a\<^sub>2) =
    (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
      (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N (n\<^sub>1 * n\<^sub>2) |
      (b\<^sub>1, b\<^sub>2) \<Rightarrow> Times b\<^sub>1 b\<^sub>2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
    apply (auto split: aexp.split)
  done

lemma aval_plus: "aval (plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"
  apply (induction a\<^sub>1 a\<^sub>2 rule: plus.induct)
              apply auto
  done

lemma aval_times: "aval (times a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s * aval a\<^sub>2 s"
  apply (induction a\<^sub>1 a\<^sub>2 rule: times.induct)
              apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
  "asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"

lemma aval_asimp [simp]: "aval (asimp a) s = aval a s"
  apply (induction a)
    apply (auto simp add: aval_plus aval_times)
  done

end