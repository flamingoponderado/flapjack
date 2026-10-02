load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _=capture "line_ok_pre_light_imp_line_ok" line_ok_pre_light_imp_line_ok;
val _=types "line_ok_pre_light_imp_line_ok_types" line_ok_pre_light_imp_line_ok;
val _=capture "all_enc_ok_pre_light_imp_all_enc_ok" all_enc_ok_pre_light_imp_all_enc_ok;
val _=types "all_enc_ok_pre_light_imp_all_enc_ok_types" all_enc_ok_pre_light_imp_all_enc_ok;
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
val _ = observe "label_six_guards" ``line_ok_pre ^cfg (Label 1 5 0) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (Label 1 5 0) /\ line_offset_ok ^labs ^ffis 4 ((Label 1 5 0) : 8 line) /\ line_labs_exist ^labs (Label 1 5 0) /\ line_ok_light ^cfg (Label 1 5 0) /\ (is_Label (Label 1 5 0) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (Label 1 5 0)``;
val _ = observe "asm_six_guards" ``line_ok_pre ^cfg (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) /\ line_offset_ok ^labs ^ffis 4 ((Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) : 8 line) /\ line_labs_exist ^labs (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) /\ line_ok_light ^cfg (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) /\ (is_Label (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (Asm (Asmi (Inst Skip)) [0w;0w;0w;0w] 4)``;
val _ = observe "halt_six_guards" ``line_ok_pre ^cfg (LabAsm Halt 236w [236w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm Halt 236w [236w;99w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm Halt 236w [236w;99w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm Halt 236w [236w;99w] 2) /\ line_ok_light ^cfg (LabAsm Halt 236w [236w;99w] 2) /\ (is_Label (LabAsm Halt 236w [236w;99w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm Halt 236w [236w;99w] 2)``;
val _ = observe "install_six_guards" ``line_ok_pre ^cfg (LabAsm Install 220w [220w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm Install 220w [220w;99w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm Install 220w [220w;99w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm Install 220w [220w;99w] 2) /\ line_ok_light ^cfg (LabAsm Install 220w [220w;99w] 2) /\ (is_Label (LabAsm Install 220w [220w;99w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm Install 220w [220w;99w] 2)``;
val _ = observe "ffi_six_guards" ``line_ok_pre ^cfg (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) /\ line_ok_light ^cfg (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) /\ (is_Label (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm (CallFFI (implode "b")) 188w [188w;99w] 2)``;
val _ = observe "jump_six_guards" ``line_ok_pre ^cfg (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) /\ line_ok_light ^cfg (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) /\ (is_Label (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm (Jump (Lab 1 5)) 16w [16w;99w] 2)``;
val _ = observe "jumpcmp_six_guards" ``line_ok_pre ^cfg (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) /\ line_ok_light ^cfg (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) /\ (is_Label (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm (JumpCmp Equal 2 (Imm 1w) (Lab 1 5)) 16w [16w;88w] 2)``;
val _ = observe "loc_six_guards" ``line_ok_pre ^cfg (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) /\ line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) /\ line_offset_ok ^labs ^ffis 4 ((LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) : 8 line) /\ line_labs_exist ^labs (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) /\ line_ok_light ^cfg (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) /\ (is_Label (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2) ==> EVEN 4) /\ line_ok ^cfg ^labs ^ffis 4 (LabAsm (LocValue 2 (Lab 1 5)) 16w [16w;77w] 2)``;
val _ = observe "odd_empty_section" ``~even_labels_strong 3 [Section 1 ([]:8 line list)] /\ ~all_enc_ok ^cfg ^labs ^ffis 3 [Section 1 []]``;
val _ = observe "call_light_guard" ``line_enc_with_nop ^cfg.encode ^labs ^ffis 4 (LabAsm (Call (Lab 1 5)) 16w [0w;0w] 2) /\ ~line_ok_light ^cfg (LabAsm (Call (Lab 1 5)) 16w [0w;0w] 2) /\ ~line_ok ^cfg ^labs ^ffis 4 (LabAsm (Call (Lab 1 5)) 16w [0w;0w] 2)``;
val mixed = ``[Section 1 [Label 1 5 0;Asm (Asmi (Inst Skip)) [0w;0w] 2;LabAsm (Jump (Lab 1 5)) 14w [14w;99w] 2;Label 1 6 0]] : 8 sec list``;
val _ = observe "code_six_guards" ``all_enc_with_nop ^cfg.encode ^labs ^ffis 4 ^mixed /\ all_enc_ok_pre ^cfg ^mixed /\ all_enc_ok_light ^cfg ^mixed /\ even_labels_strong 4 ^mixed /\ all_labs_exist ^labs ^mixed /\ offset_ok ^labs ^ffis 4 ^mixed /\ all_enc_ok ^cfg ^labs ^ffis 4 ^mixed``;
