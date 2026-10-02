load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labSemTheory asmTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val lab_lookup_IMP_source = prove (``(lab_lookup l1 l2 labs = SOME x) ==> (find_pos (Lab l1 l2) labs = x)``,
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);
val _ = capture "lab_lookup_def" lab_lookup_def;
val _ = captureTypes "lab_lookup_def_types" lab_lookup_def;
val _ = capture "lab_lookup_IMP" lab_lookup_IMP_source;
val _ = captureTypes "lab_lookup_IMP_types" lab_lookup_IMP_source;
val _ = capture "line_ok_def" line_ok_def;
val _ = captureTypes "line_ok_def_types" line_ok_def;
val _ = capture "lines_ok_def" lines_ok_def;
val _ = captureTypes "lines_ok_def_types" lines_ok_def;
val _ = capture "all_enc_ok_def" all_enc_ok_def;
val _ = captureTypes "all_enc_ok_def_types" all_enc_ok_def;
val _ = capture "all_enc_ok_cons" all_enc_ok_cons;
val _ = captureTypes "all_enc_ok_cons_types" all_enc_ok_cons;
val _ = capture "all_enc_ok_imp_sec_label_zero" all_enc_ok_imp_sec_label_zero;
val _ = captureTypes "all_enc_ok_imp_sec_label_zero_types" all_enc_ok_imp_sec_label_zero;
val _ = capture "pos_val_0" pos_val_0;
val _ = captureTypes "pos_val_0_types" pos_val_0;
val _ = capture "pos_val_bound" pos_val_bound;
val _ = captureTypes "pos_val_bound_types" pos_val_bound;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((SIMP_CONV (srw_ss()) [] THENC EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL) q)); print "\n");
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
val _ = observe "lookup_generic_bool" ``lab_lookup 1 5 (insert 1 (insert 5 T LN) LN) = SOME T``;
val _ = observe "lookup_outer_missing" ``lab_lookup 2 5 ^labs = NONE``;
val _ = observe "lookup_inner_missing" ``lab_lookup 1 6 ^labs = NONE``;
val _ = observe "label_even" ``line_ok ^cfg ^labs ^ffis 4 (Label 1 5 0)``;
val _ = observe "label_odd" ``line_ok ^cfg ^labs ^ffis 3 (Label 1 5 0) = F``;
val _ = observe "label_nonzero" ``line_ok ^cfg ^labs ^ffis 4 (Label 1 5 2) = F``;
val _ = observe "asm_skip" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w] 2)``;
val _ = observe "asm_padding" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4)``;
val _ = observe "asm_bad_length" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w] 3) = F``;
val _ = observe "asm_bad_bytes" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [1w;1w] 2) = F``;
val _ = observe "asm_bad_reg" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst (Const 40 1w))) [10w;11w] 2) = F``;
val _ = observe "asm_cbw" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Cbw 1 2) [10w;11w] 2)``;
val _ = observe "lab_halt" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm Halt 99w [236w;99w] 2)``;
val _ = observe "lab_install" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm Install 99w [220w;99w] 2)``;
val _ = observe "lab_ffi_index" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (CallFFI (implode "b")) 99w [188w;99w] 2)``;
val _ = observe "lab_ffi_missing_default" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (CallFFI (implode "z")) 99w [204w;99w] 2)``;
val _ = observe "lab_call_unsupported" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (Call (Lab 1 5)) 0w [16w;99w] 2) = F``;
val _ = observe "lab_jump" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (Jump (Lab 1 5)) 99w [16w;99w] 2)``;
val _ = observe "lab_jump_cmp" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 99w [16w;88w] 2)``;
val _ = observe "lab_loc" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (LocValue 2 (Lab 1 5)) 99w [16w;77w] 2)``;
val _ = observe "lab_missing_label" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (Jump (Lab 1 6)) 0w [0w;99w] 2) = F``;
val _ = observe "all_empty" ``all_enc_ok ^cfg ^labs ^ffis 3 ([]:8 labLang$prog)``;
val _ = observe "all_empty_section_even" ``all_enc_ok ^cfg ^labs ^ffis 4 [Section 1 []:8 labLang$sec]``;
val _ = observe "all_empty_section_odd" ``all_enc_ok ^cfg ^labs ^ffis 3 [Section 1 []:8 labLang$sec] = F``;
val _ = observe "all_code_valid" ``all_enc_ok ^cfg ^labs ^ffis 0 ^code``;
val _ = observe "all_code_bytes" ``LENGTH(prog_to_bytes ^code) = 4``;
val _ = observe "all_zero_position" ``pos_val 0 0 ^code = 0``;
val _ = observe "independent_bound_position" ``pos_val 2 17 ^code = 21``;
