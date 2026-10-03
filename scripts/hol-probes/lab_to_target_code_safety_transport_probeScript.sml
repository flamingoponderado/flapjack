load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory labLangTheory labSemTheory labPropsTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t = DB.fetch "lab_to_targetProof" "code_similar_IMP_both_no_share_mem";
val _ = capture "code_similar_IMP_both_no_share_mem" t;
val _ = types "code_similar_IMP_both_no_share_mem_types" t;
val _ = print("code_similar_IMP_both_no_share_mem_hypotheses=" ^ Int.toString(length(hyp t)) ^ "\n");
val _ = show_types := false;
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO th))); print "\n");
val src = ``[Section 0 [Asm (Asmi (Inst Skip)) [] 0]] : 8 sec list``;
val dst = ``[Section 0 [Asm (Asmi (Inst Skip)) [1w;255w] 7]] : 8 sec list``;
val hs = prove(``code_similar ^src ^dst /\ no_share_mem_inst ^src``,
  rw [code_similar_def, line_similar_def, no_share_mem_inst_def, asm_fetch_aux_def]);
val _ = checked "changed_bytes_length_safe" (MATCH_MP (INST [
  mk_var("code",type_of src) |-> src, mk_var("sec_list",type_of dst) |-> dst]
  (INST_TYPE [alpha |-> ``:8``] t)) hs);
val _ = checked "instruction_change_rejected" (prove(
  ``~code_similar ^src [Section 0 [Asm (ShareMem asm$Load 1 (Addr 2 0w)) [] 0]]``,
  simp [code_similar_def, line_similar_def]));
