theory Short_Theory_ASM
  imports "HOL-IMP.AExp"
begin

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 (LOADI n) _ stk = Some (n # stk)" |
  "exec1 (LOAD x) s stk = Some (s x # stk)" |
  "exec1 ADD _ (j # i # stk) = Some ((i + j) # stk)" |
  "exec1 ADD _ _ = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stk = Some stk" |
  "exec (i # is) s stk =
    (case exec1 i s stk of
      Some stk\<^sub>i \<Rightarrow> exec is s stk\<^sub>i |
      None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]" |
  "comp (V x) = [LOAD x]" |
  "comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

lemma exec_app: "exec (is\<^sub>1 @ is\<^sub>2) s stk =
  (case exec is\<^sub>1 s stk of
    Some stk\<^sub>1 \<Rightarrow> exec is\<^sub>2 s stk\<^sub>1 |
    None \<Rightarrow> None)"
  apply (induction is\<^sub>1 arbitrary: stk)
   apply (auto split: option.split)
  done

lemma "exec (comp a) s stk = Some (aval a s # stk)"
  apply (induction a arbitrary: stk)
    apply (auto simp add: exec_app)
  done

end