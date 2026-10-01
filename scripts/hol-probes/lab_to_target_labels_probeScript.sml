load "bossLib";
load "preamble";
load "lab_to_targetTheory";
open bossLib HolKernel Parse preamble lab_to_targetTheory labLangTheory miscTheory ffiTheory;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val _ = observe "sl_nil" ``section_labels 0 ([] : 8 line list) [] = (0,[])``;
val _ = observe "sl_mix" ``section_labels 5 [Label 1 2 3; Asm (Asmi (Inst Skip)) [] 4; Label 1 0 2] [] = (14,[(2,8)])``;
val _ = observe "sl_zero_only" ``section_labels 0 [Label 1 0 7] [] = (7,[])``;
val _ = observe "cl_empty" ``compute_labels_alt 0 ([] : 8 sec list) LN = LN``;
val _ = observe "cl_lookup" ``lookup_any 2 (lookup_any 7 (compute_labels_alt 0 [Section 7 [Label 7 2 3; Asm (Asmi (Inst Skip)) [] 4]] LN) LN) 0 = 3``;
val _ = observe "cl_base_lookup" ``lookup_any 0 (lookup_any 7 (compute_labels_alt 0 [Section 7 [Label 7 2 3]] LN) LN) 0 = 0``;

