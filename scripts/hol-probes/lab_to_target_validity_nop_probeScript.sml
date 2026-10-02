load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "line_ok_line_enc_with_nop" line_ok_line_enc_with_nop;
val _ = types "line_ok_line_enc_with_nop_types" line_ok_line_enc_with_nop;
val _ = capture "lines_ok_lines_enc_with_nop" lines_ok_lines_enc_with_nop;
val _ = types "lines_ok_lines_enc_with_nop_types" lines_ok_lines_enc_with_nop;
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
val _ = observe "label_full" ``line_ok ^cfg ^labs ^ffis 4 (Label 1 5 0) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (Label 1 5 0)``;
val _ = observe "asm_padding_full" ``line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4)``;
val _ = observe "halt_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm Halt 99w [236w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm Halt 99w [236w;99w] 2)``;
val _ = observe "install_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm Install 99w [220w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm Install 99w [220w;99w] 2)``;
val _ = observe "ffi_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (CallFFI (implode "b")) 99w [188w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (CallFFI (implode "b")) 99w [188w;99w] 2)``;
val _ = observe "jump_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (Jump (Lab 1 5)) 99w [16w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (Jump (Lab 1 5)) 99w [16w;99w] 2)``;
val _ = observe "jumpcmp_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 99w [16w;88w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 99w [16w;88w] 2)``;
val _ = observe "loc_full" ``line_ok ^cfg ^labs ^ffis 4 (LabAsm (LocValue 2 (Lab 1 5)) 99w [16w;77w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (LocValue 2 (Lab 1 5)) 99w [16w;77w] 2)``;
val _ = observe "list_actual_full" ``lines_ok ^cfg ^labs ^ffis 4 [Label 1 5 0;Asm (Asmi (Inst Skip)) [0w;0w] 2;LabAsm (Jump (Lab 1 5)) 99w [14w;99w] 2] /\ lines_enc_with_nop ^cfg.encode ^labs ^ffis 4 [Label 1 5 0;Asm (Asmi (Inst Skip)) [0w;0w] 2;LabAsm (Jump (Lab 1 5)) 99w [14w;99w] 2]``;
