theory Short_Theory_13_2
  imports "HOL-IMP.BExp"
begin

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | Or     com com          ("_/ OR _" [60, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)

text \<open>acom is the type of annotated commands (wrt. a type of annotation)\<close>
datatype 'a acom =
  SKIP 'a                           ("SKIP {_}" 61) |
  Assign vname aexp 'a              ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Seq "('a acom)" "('a acom)"       ("_;;//_"  [60, 61] 60) |
  If bexp 'a "'a acom" 'a "'a acom" 'a
    ("(IF _/ THEN ({_}/ _)/ ELSE ({_}/ _)//{_})"  [0, 0, 0, 61, 0, 0] 61) |
  Or "'a acom" "'a acom" 'a
    ("_ OR// _//{_}" [60, 61, 0] 60) |
  While 'a bexp 'a "'a acom" 'a
    ("({_}//WHILE _//DO ({_}//_)//{_})"  [0, 0, 0, 61, 0] 61)

notation com.SKIP ("SKIP")

text \<open>strip maps acoms back to the original commands\<close>
text_raw\<open>\snip{stripdef}{1}{1}{%\<close>
fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = SKIP" |
"strip (x ::= e {P}) = x ::= e" |
"strip (C\<^sub>1;;C\<^sub>2) = strip C\<^sub>1;; strip C\<^sub>2" |
"strip (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {P}) =
  IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2" |
"strip (C\<^sub>1 OR C\<^sub>2 {P}) = strip C\<^sub>1 OR strip C\<^sub>2" |
"strip ({I} WHILE b DO {P} C {Q}) = WHILE b DO strip C"
text_raw\<open>}%endsnip\<close>

text \<open>asize counts the number of annotations that a com admits\<close>
text_raw\<open>\snip{asizedef}{1}{1}{%\<close>
fun asize :: "com \<Rightarrow> nat" where
"asize SKIP = 1" |
"asize (x ::= e) = 1" |
"asize (C\<^sub>1;;C\<^sub>2) = asize C\<^sub>1 + asize C\<^sub>2" |
"asize (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = asize C\<^sub>1 + asize C\<^sub>2 + 3" |
"asize (C\<^sub>1 OR C\<^sub>2) = asize C\<^sub>1 + asize C\<^sub>2 + 1" |
"asize (WHILE b DO C) = asize C + 3"
text_raw\<open>}%endsnip\<close>

text \<open>shift eats the first n elements of a sequence\<close>
text_raw\<open>\snip{annotatedef}{1}{1}{%\<close>
definition shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
"shift f n = (\<lambda>p. f(p+n))"

text \<open>Defined in terms of shift, annotate annotates a command c with a sequence of annotations\<close>
fun annotate :: "(nat \<Rightarrow> 'a) \<Rightarrow> com \<Rightarrow> 'a acom" where
"annotate f SKIP = SKIP {f 0}" |
"annotate f (x ::= e) = x ::= e {f 0}" |
"annotate f (c\<^sub>1;;c\<^sub>2) = annotate f c\<^sub>1;; annotate (shift f (asize c\<^sub>1)) c\<^sub>2" |
"annotate f (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  IF b THEN {f 0} annotate (shift f 1) c\<^sub>1
  ELSE {f(asize c\<^sub>1 + 1)} annotate (shift f (asize c\<^sub>1 + 2)) c\<^sub>2
  {f(asize c\<^sub>1 + asize c\<^sub>2 + 2)}" |
"annotate f (c\<^sub>1 OR c\<^sub>2) =
  annotate f c\<^sub>1 OR annotate (shift f (asize c\<^sub>1)) c\<^sub>2 {f (asize c\<^sub>1 + asize c\<^sub>2)}" |
"annotate f (WHILE b DO c) =
  {f 0} WHILE b DO {f 1} annotate (shift f 2) c {f(asize c + 2)}"
text_raw\<open>}%endsnip\<close>

text \<open>annos collects a command's annotations into a list\<close>
text_raw\<open>\snip{annosdef}{1}{1}{%\<close>
fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {P}) = [P]" |
"annos (x ::= e {P}) = [P]" |
"annos (C\<^sub>1;;C\<^sub>2) = annos C\<^sub>1 @ annos C\<^sub>2" |
"annos (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {Q}) =
  P\<^sub>1 # annos C\<^sub>1 @  P\<^sub>2 # annos C\<^sub>2 @ [Q]" |
"annos (C\<^sub>1 OR C\<^sub>2 {P}) = annos C\<^sub>1 @ annos C\<^sub>2 @ [P]" |
"annos ({I} WHILE b DO {P} C {Q}) = I # P # annos C @ [Q]"
text_raw\<open>}%endsnip\<close>

text \<open>anno retrives the pth annotation of a command, by first collecting its annotations then
indexing into the pth list element\<close>
definition anno :: "'a acom \<Rightarrow> nat \<Rightarrow> 'a" where
"anno C p = annos C ! p"

text \<open>post retrieves the last annotation of a command, by first collecting its annotations\<close>
definition post :: "'a acom \<Rightarrow>'a" where
"post C = last(annos C)"

text \<open>map_acom maps the annotations of an acom\<close>
text_raw\<open>\snip{mapacomdef}{1}{2}{%\<close>
fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {P}) = SKIP {f P}" |
"map_acom f (x ::= e {P}) = x ::= e {f P}" |
"map_acom f (C\<^sub>1;;C\<^sub>2) = map_acom f C\<^sub>1;; map_acom f C\<^sub>2" |
"map_acom f (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {Q}) =
  IF b THEN {f P\<^sub>1} map_acom f C\<^sub>1 ELSE {f P\<^sub>2} map_acom f C\<^sub>2
  {f Q}" |
"map_acom f (C\<^sub>1 OR C\<^sub>2 {P}) = map_acom f C\<^sub>1 OR map_acom f C\<^sub>2 {f P}" |
"map_acom f ({I} WHILE b DO {P} C {Q}) =
  {f I} WHILE b DO {f P} map_acom f C {f Q}"
text_raw\<open>}%endsnip\<close>

text \<open>the list of annotations for any command is always nonempty\<close>
lemma annos_ne: "annos C \<noteq> []"
by(induction C) auto

text \<open>stripping a command that has been annotated recovers it\<close>
lemma strip_annotate[simp]: "strip(annotate f c) = c"
by(induction c arbitrary: f) auto

text \<open>the list of annotations of a com, once annotated, is as large as the number of annotations it admits\<close>
lemma length_annos_annotate[simp]: "length (annos (annotate f c)) = asize c"
by(induction c arbitrary: f) auto

text \<open>the size of the list of annotations of a command is as large as the number of annotations its underlying com admits\<close>
lemma size_annos: "size(annos C) = asize(strip C)"
by(induction C)(auto)

text \<open>if two acom share the same com, then they have the same number of annotations\<close>
lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply(case_tac C1, simp_all)+
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

text \<open>dually, the pth annotation is the pth element of the annotating sequence\<close>
lemma anno_annotate[simp]: "p < asize c \<Longrightarrow> anno (annotate f c) p = f p"
proof (induction c arbitrary: f p)
  case SKIP
  then show ?case by (auto simp: anno_def)
next
  case (Assign x1 x2)
  then show ?case by (auto simp: anno_def)
next
  case (Seq c1 c2)
  then show ?case by (auto simp: anno_def nth_append shift_def)
next
  case (If x1 c1 c2)
  then show ?case
    by (auto simp: anno_def nth_append nth_Cons shift_def split: nat.split,
        metis add_Suc_right add_diff_inverse add.commute,
        rule_tac f=f in arg_cong,
        arith)
next
  case (Or c1 c2)
  then show ?case
    by (auto simp: anno_def nth_append shift_def,
        rule_tac f=f in arg_cong,
        arith)
next
case (While x1 c)
  then show ?case
    by (auto simp: anno_def nth_append nth_Cons shift_def
        split: nat.split, rule_tac f=f in arg_cong,
        arith)
qed

text \<open>two acoms are equal iff they have the same underlying command and same list of annotations\<close>
text \<open>Proof is by inductive definiton of acom, and list lemmas / annos lemmas\<close>
lemma eq_acom_iff_strip_annos:
  "C1 = C2 \<longleftrightarrow> strip C1 = strip C2 \<and> annos C1 = annos C2"
apply(induction C1 arbitrary: C2)
apply(case_tac C2, auto simp: size_annos_same2)+
done

text \<open>two acoms are equal iff they have the same underlying command and same sublist of annotations\<close>
lemma eq_acom_iff_strip_anno:
  "C1=C2 \<longleftrightarrow> strip C1 = strip C2 \<and> (\<forall>p<size(annos C1). anno C1 p = anno C2 p)"
by(auto simp add: eq_acom_iff_strip_annos anno_def
     list_eq_iff_nth_eq size_annos_same2)

text \<open>the last annotation after mapping through f is exactly the last annotation, then mapping it by f\<close>
lemma post_map_acom[simp]: "post(map_acom f C) = f(post C)"
by (induction C) (auto simp: post_def last_append annos_ne)

text \<open>the underlying command is unchanged by map_acom\<close>
lemma strip_map_acom[simp]: "strip (map_acom f C) = strip C"
by (induction C) auto

text \<open>the pth annotation after mapping through f is exactly the pth annotation, then mapping it by f\<close>
lemma anno_map_acom: "p < size(annos C) \<Longrightarrow> anno (map_acom f C) p = f(anno C p)"
apply(induction C arbitrary: p)
apply(auto simp: anno_def nth_append nth_Cons' size_annos)
done

text \<open>inversion lemma for strip C\<close>

lemma strip_eq_SKIP:
  "strip C = SKIP \<longleftrightarrow> (\<exists>P. C = SKIP {P})"
by (cases C) simp_all

lemma strip_eq_Assign:
  "strip C = x::=e \<longleftrightarrow> (\<exists>P. C = x::=e {P})"
by (cases C) simp_all

lemma strip_eq_Seq:
  "strip C = c1;;c2 \<longleftrightarrow> (\<exists>C1 C2. C = C1;;C2 & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_If:
  "strip C = IF b THEN c1 ELSE c2 \<longleftrightarrow>
  (\<exists>P1 P2 C1 C2 Q. C = IF b THEN {P1} C1 ELSE {P2} C2 {Q} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_Or:
  "strip C = c1 OR c2 \<longleftrightarrow>
  (\<exists>C1 C2 P. C = C1 OR C2 {P} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_While:
  "strip C = WHILE b DO c1 \<longleftrightarrow>
  (\<exists>I P C1 Q. C = {I} WHILE b DO {P} C1 {Q} & strip C1 = c1)"
by (cases C) simp_all

text \<open>shifting a constant sequence does nothing\<close>
lemma [simp]: "shift (\<lambda>p. a) n = (\<lambda>p. a)"
by(simp add:shift_def)

text \<open>the set of all members of an acom created by annotate with a constant sequence on that annotation is a singleton\<close>
lemma set_annos_anno[simp]: "set (annos (annotate (\<lambda>p. a) c)) = {a}"
  by(induction c) simp_all

text \<open>the last annotation of an acom is in the set of list of annotations of that acom\<close>
lemma post_in_annos: "post C \<in> set(annos C)"
by(auto simp: post_def annos_ne)

text \<open>the last annotation of C is the last element of the list of annotations generated from C.\<close>
lemma post_anno_asize: "post C = anno C (size(annos C) - 1)"
  by(simp add: post_def last_conv_nth[OF annos_ne] anno_def)

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

end