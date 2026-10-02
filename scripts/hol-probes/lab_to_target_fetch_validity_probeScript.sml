load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labSemTheory asmTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "fetch_validity" all_enc_ok_asm_fetch_aux_IMP_line_ok;
val _ = captureTypes "fetch_validity_types" all_enc_ok_asm_fetch_aux_IMP_line_ok;
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
val _ = observe "valid_code" ``all_enc_ok ^cfg ^labs ^ffis 0 ^code``;
val _ = observe "fetch_zero" ``asm_fetch_aux 0 ^code = SOME (Asm (Asmi (Inst Skip)) [0w;0w] 2)``;
val _ = observe "fetch_one" ``asm_fetch_aux 1 ^code = SOME (LabAsm Halt 99w [238w;99w] 2)``;
val _ = observe "fetch_end" ``asm_fetch_aux 2 ^code = NONE``;
val _ = observe "fetched_valid" ``line_ok ^cfg ^labs ^ffis (pos_val 1 0 ^code) (LabAsm Halt 99w [238w;99w] 2)``;
