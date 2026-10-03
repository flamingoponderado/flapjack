load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t=DB.fetch "misc" "find_index_MEM";
val _=capture "find_index_MEM" t;
val _=types "find_index_MEM_types" t;
val _=print("find_index_MEM_hypotheses="^Int.toString(length(hyp t))^"\n");
val _=show_types:=false;
fun checked label th=(print(label^"=");print_term(rhs(concl(EQT_INTRO th)));print"\n");
fun instanceCase label values target offset =
 let val th=ISPECL [values,target,offset] (DB.fetch "misc" "find_index_MEM")
     val guard=fst(dest_imp(concl th))
 in checked label (MP th (EQT_ELIM(EVAL guard))) end;
val _=instanceCase "first" ``[7;13]:num list`` ``7:num`` ``0:num``;
val _=instanceCase "last" ``[7;13]:num list`` ``13:num`` ``0:num``;
val _=instanceCase "offset" ``[7;13]:num list`` ``13:num`` ``10:num``;
val _=instanceCase "duplicate" ``[7;7]:num list`` ``7:num`` ``10:num``;
val _=instanceCase "large" ``[7;13]:num list`` ``13:num`` ``1208925819614629174706176:num``;
val _=instanceCase "strings" ``["a";"b";"b"]`` ``"b"`` ``10:num``;
val _=instanceCase "words" ``[7w;13w]:80 word list`` ``13w:80 word`` ``10:num``;
fun observe label q=(print(label^"=");print_term(rconc((EVAL THENC QCONV(SIMP_CONV bool_ss [])) q));print"\n");
val _=observe "missing_guard" ``~MEM (8:num) [7;13]``;
val _=observe "empty_guard" ``~MEM (7:num) []``;
