load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labSemTheory asmTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "good_code_def" good_code_def;
val _ = captureTypes "good_code_def_types" good_code_def;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(
 (SIMP_CONV (srw_ss()) [good_code_def, extract_labels_def, sec_ends_with_label_def,
  sec_labels_ok_def, sec_label_ok_def, get_labels_def, sec_get_labels_def,
  line_get_labels_def, labs_of_def, get_code_labels_def, sec_get_code_labels_def,
  line_get_code_labels_def, backendPropsTheory.restrict_nonzero_def,
  labs_domain_insert, labs_domain_LN, sptreeTheory.domain_insert,
  labPropsTheory.sec_ok_pre_def, labPropsTheory.line_ok_pre_def]
  THENC EVAL THENC SIMP_CONV (srw_ss()) [pred_setTheory.SUBSET_DEF, pred_setTheory.GSPECIFICATION, pred_setTheory.EXTENSION] THENC EVAL) q)); print "\n");
val cfg = ``<| ISA := RISC_V; encode := (λa. case a of
 Inst Skip => [0w;0w] | Jump w => [w2w w;99w]
 | JumpCmp c r ri w => [w2w w;88w] | Loc r w => [w2w w;77w]
 | _ => [10w;11w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (128w,127w); hw_offset := (128w,127w); byte_offset := (128w,127w);
 jump_offset := (128w,127w); cjump_offset := (128w,127w); loc_offset := (128w,127w)
 |> : 8 asm_config``;
val labs = ``insert 1 (insert 5 20 LN) LN : num num_map num_map``;
val ffis = ``[ExtCall (implode "a"); ExtCall (implode "b")]``;
val code = ``[Section 1 [Label 1 5 0; Asm (Asmi (Inst Skip)) [0w;0w] 2;
 LabAsm Halt 99w [238w;99w] 2]; Section 2 []] : 8 labLang$prog``;
val cache = ``insert 3 (insert 4 F LN) LN : bool num_map num_map``;
val code = ``[Section 1 [Label 1 1 5]] : 8 labLang$prog``;
val refs = ``[Section 1 [LabAsm (Jump (Lab 3 4)) 99w [] 0; Label 1 1 0]] : 8 labLang$prog``;
val empty = ``LN : bool num_map num_map``;
val _ = observe "empty_code" ``good_code ^cfg ^empty ([]:8 labLang$prog)``;
val _ = observe "empty_section_rejected" ``good_code ^cfg ^empty [Section 1 []:8 labLang$sec] = F``;
val _ = observe "generic_value_code" ``good_code ^cfg ^empty ^code``;
val _ = observe "wrong_section_label" ``good_code ^cfg ^empty [Section 1 [Label 2 1 0]:8 labLang$sec] = F``;
val _ = observe "zero_label_rejected" ``good_code ^cfg ^empty [Section 1 [Label 1 0 0]:8 labLang$sec] = F``;
val _ = observe "duplicate_sections" ``good_code ^cfg ^empty [Section 1 [Label 1 1 0]; Section 1 [Label 1 2 0]:8 labLang$sec] = F``;
val _ = observe "duplicate_labels" ``good_code ^cfg ^empty [Section 1 [Label 1 1 0; Label 1 1 7]:8 labLang$sec] = F``;
val _ = observe "nonlabel_end" ``good_code ^cfg ^empty [Section 1 [Label 1 1 0; Asm (Asmi (Inst Skip)) [] 0]:8 labLang$sec] = F``;
val _ = observe "missing_nonzero_reference" ``good_code ^cfg ^empty ^refs = F``;
val _ = observe "boolean_value_label_hit" ``good_code ^cfg ^cache ^refs``;
val _ = observe "outer_domain_clash" ``good_code ^cfg (insert 1 (LN:bool num_map) LN) ^code = F``;
val _ = observe "zero_reference_unrestricted" ``good_code ^cfg ^empty [Section 1 [LabAsm (Jump (Lab 3 0)) 99w [] 0; Label 1 1 0]:8 labLang$sec]``;
val _ = observe "call_reference_ignored" ``good_code ^cfg ^empty [Section 1 [LabAsm (Call (Lab 3 4)) 99w [] 0; Label 1 1 0]:8 labLang$sec]``;
val _ = observe "encoding_cache_unchecked" ``good_code ^cfg ^empty [Section 1 [Asm (Asmi (Inst Skip)) [255w] 37; Label 1 1 0]:8 labLang$sec]``;
val _ = observe "bad_register_precondition" ``good_code ^cfg ^empty [Section 1 [Asm (Asmi (Inst (Const 40 1w))) [] 0; Label 1 1 0]:8 labLang$sec] = F``;
