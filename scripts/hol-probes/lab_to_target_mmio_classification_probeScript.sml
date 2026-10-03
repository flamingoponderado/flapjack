load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t=DB.fetch "lab_to_targetProof" "mmio_pcs_min_index_is_SOME";
val _=capture "mmio_pcs_min_index_is_SOME" t;
val _=types "mmio_pcs_min_index_is_SOME_types" t;
val _=print("mmio_pcs_min_index_is_SOME_hypotheses="^Int.toString(length(hyp t))^"\n");
val _=show_types:=false;
fun checked label th=(print(label^"=");print_term(rhs(concl(EQT_INTRO th)));print"\n");
fun discharge th = MP th (prove(fst(dest_imp(concl th)), simp [] >> EVAL_TAC >> simp []));
fun instanceCase label prefix suffix =
 let val hs=discharge (INST [``ffis:ffiname list`` |-> prefix,``l:ffiname list`` |-> suffix] mmio_pcs_min_index_APPEND_thm)
     val (application,result)=dest_eq(concl hs)
     val names=rand application
     val index=rand result
     val source=INST [``i:num`` |-> index] (SPEC names t)
 in checked label (MP source hs) end;
val guest=``ExtCall(strlit "guest")``;
val _=instanceCase "empty" ``[]:ffiname list`` ``[]:ffiname list``;
val _=instanceCase "external" ``[^guest]`` ``[]:ffiname list``;
val _=instanceCase "read" ``[]:ffiname list`` ``[SharedMem MappedRead]``;
val _=instanceCase "write" ``[]:ffiname list`` ``[SharedMem MappedWrite]``;
val _=instanceCase "mixed" ``[^guest]`` ``[SharedMem MappedRead;SharedMem MappedWrite]``;
val _=instanceCase "duplicate" ``[^guest;^guest]`` ``[SharedMem MappedRead;SharedMem MappedWrite]``;
val _=instanceCase "four_external" ``[^guest;^guest;^guest;^guest]`` ``[SharedMem MappedRead]``;
fun observe label q=checked label (prove(q, simp [] >> EVAL_TAC >> simp []));
val _=observe "length_guard" ``~(3 <= LENGTH [^guest])``;
val _=observe "prefix_guard" ``~(?s. EL 0 [SharedMem MappedRead] = ExtCall s)``;
