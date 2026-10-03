(* Complete original padding similarity statements/types and concrete padding.
Local lemma is replayed verbatim, not claimed to be an exported theorem. *)
load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory;
val local_add_nop = prove (``  ∀ls ls' h.
  LIST_REL line_similar ls ls' ⇒
  LIST_REL line_similar ls (add_nop h ls')``,
  Induct_on`ls`>>rw[add_nop_def]>>
  Cases_on`y`>>Cases_on`h`>>fs[add_nop_def,line_similar_def]);
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "ps_add" local_add_nop;
val _ = captureTypes "ps_add_types" local_add_nop;
val _ = capture "ps_section" (DB.fetch "lab_to_targetProof" "line_similar_pad_section");
val _ = captureTypes "ps_section_types" (DB.fetch "lab_to_targetProof" "line_similar_pad_section");
val _ = capture "ps_code" (DB.fetch "lab_to_targetProof" "code_similar_pad_code");
val _ = captureTypes "ps_code_types" (DB.fetch "lab_to_targetProof" "code_similar_pad_code");
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "ps_add_value" ``add_nop [7w] ([Label 1 2 9; Asm (Asmi (asm$Inst asm$Skip)) [1w] 1; LabAsm (Jump (Lab 1 2)) 13w [2w] 1] : 8 line list)``;
val _ = observe "ps_section_value" ``pad_section [7w] ([Label 1 2 9; Asm (Asmi (asm$Inst asm$Skip)) [1w] 1; LabAsm (Jump (Lab 1 2)) 13w [2w] 1] : 8 line list) []``;
val _ = observe "ps_empty_nop" ``pad_section [] ([Label 1 2 9; Asm (Asmi (asm$Inst asm$Skip)) [1w] 1; LabAsm (Jump (Lab 1 2)) 13w [2w] 1] : 8 line list) []``;
val _ = observe "ps_acc_value" ``pad_section [7w] ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [] 2] : 8 line list) [LabAsm (Jump (Lab 1 2)) 19w [4w] 1]``;
val _ = observe "ps_label_only" ``pad_section [7w] ([Label 1 2 9;Label 1 3 0] : 8 line list) []``;
val _ = observe "ps_code_similar" ``code_similar [Section 4 ([Label 1 2 9; Asm (Asmi (asm$Inst asm$Skip)) [1w] 1; LabAsm (Jump (Lab 1 2)) 13w [2w] 1] : 8 line list)] (pad_code [7w] [Section 4 ([Label 1 2 9; Asm (Asmi (asm$Inst asm$Skip)) [1w] 1; LabAsm (Jump (Lab 1 2)) 13w [2w] 1] : 8 line list)])``;
