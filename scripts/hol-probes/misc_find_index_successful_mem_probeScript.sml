load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t=DB.fetch "misc" "find_index_is_MEM";
val _=capture "find_index_is_MEM" t;
val _=types "find_index_is_MEM_types" t;
val _=print("find_index_is_MEM_hypotheses="^Int.toString(length(hyp t))^"\n");
val _=show_types:=false;
fun checked label th=(print(label^"=");print_term(rhs(concl(EQT_INTRO th)));print"\n");
fun instanceCase label target values offset index =
 let val th=ISPECL [target,values,offset,index] (DB.fetch "misc" "find_index_is_MEM")
     val guard=fst(dest_imp(concl th))
 in checked label (MP th (EQT_ELIM(EVAL guard))) end;
val _=instanceCase "first" ``7:num`` ``[7;13]:num list`` ``0:num`` ``0:num``;
val _=instanceCase "last" ``13:num`` ``[7;13]:num list`` ``0:num`` ``1:num``;
val _=instanceCase "offset" ``13:num`` ``[7;13]:num list`` ``10:num`` ``11:num``;
val _=instanceCase "duplicate" ``7:num`` ``[7;7]:num list`` ``10:num`` ``10:num``;
val _=instanceCase "large" ``13:num`` ``[7;13]:num list`` ``1208925819614629174706176:num`` ``1208925819614629174706177:num``;
val _=instanceCase "strings" ``"b"`` ``["a";"b";"b"]`` ``10:num`` ``11:num``;
val _=instanceCase "words" ``13w:80 word`` ``[7w;13w]:80 word list`` ``10:num`` ``11:num``;
fun observe label q=(print(label^"=");print_term(rconc((EVAL THENC QCONV(SIMP_CONV bool_ss [])) q));print"\n");
val _=observe "missing_guard" ``find_index (8:num) [7;13] 10 = NONE``;
val _=observe "empty_guard" ``find_index (7:num) [] 10 = NONE``;
