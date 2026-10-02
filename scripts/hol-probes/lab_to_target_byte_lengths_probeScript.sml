load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labSemTheory asmTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val all_enc_ok_prog_to_bytes_EVEN_source = prove
 (``!code n c labs ffi pos. EVEN pos /\ all_enc_ok c labs ffi pos code ==>
   EVEN (LENGTH (prog_to_bytes code))``,
 fs[prog_to_bytes_MAP] >>
 Induct >> fs[] >> Cases >>
 fs[all_enc_ok_cons] >> rw[EVEN_ADD] >>
 rfs[] >> fs[LENGTH_FLAT] >>
 `MAP line_length l = MAP LENGTH (MAP line_bytes l)` by
   metis_tac[lines_ok_MAP_line_byte_length] >>
 pop_assum SUBST_ALL_TAC >> simp[] >> metis_tac[EVEN_ADD]);
val _ = capture "prog_to_bytes_APPEND" prog_to_bytes_APPEND;
val _ = captureTypes "prog_to_bytes_APPEND_types" prog_to_bytes_APPEND;
val _ = capture "line_ok_line_byte_length" line_ok_line_byte_length;
val _ = captureTypes "line_ok_line_byte_length_types" line_ok_line_byte_length;
val _ = capture "lines_ok_MAP_line_byte_length" lines_ok_MAP_line_byte_length;
val _ = captureTypes "lines_ok_MAP_line_byte_length_types" lines_ok_MAP_line_byte_length;
val _ = capture "all_enc_ok_prog_to_bytes_EVEN" all_enc_ok_prog_to_bytes_EVEN_source;
val _ = captureTypes "all_enc_ok_prog_to_bytes_EVEN_types" all_enc_ok_prog_to_bytes_EVEN_source;
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
val ls = ``[Label 1 5 0; Asm (Asmi (Inst Skip)) [0w;0w] 2; LabAsm Halt 99w [238w;99w] 2] : 8 line list``;
val odd_cfg = ``(^cfg with encode := (λa. [0w]))``;
val odd_code = ``[Section 1 [Asm (Asmi (Inst Skip)) [0w] 1]] : 8 labLang$prog``;
val _ = observe "append_bytes" ``prog_to_bytes (^code ++ ^code) = prog_to_bytes ^code ++ prog_to_bytes ^code``;
val _ = observe "label_bytes" ``LENGTH(line_bytes (Label 1 5 0:8 line)) = line_length (Label 1 5 0:8 line)``;
val _ = observe "asm_bytes" ``LENGTH(line_bytes (Asm (Asmi (Inst Skip)) [0w;0w] 2:8 line)) = 2``;
val _ = observe "labasm_bytes" ``LENGTH(line_bytes (LabAsm Halt 99w [238w;99w] 2:8 line)) = 2``;
val _ = observe "map_lengths" ``MAP LENGTH (MAP line_bytes ^ls) = MAP line_length ^ls``;
val _ = observe "even_output" ``EVEN(LENGTH(prog_to_bytes ^code))``;
val _ = observe "invalid_label" ``line_ok ^cfg ^labs ^ffis 0 (Label 1 5 1) = F``;
val _ = observe "odd_start_valid" ``all_enc_ok ^odd_cfg ^labs ^ffis 1 ^odd_code``;
val _ = observe "odd_start_output" ``EVEN(LENGTH(prog_to_bytes ^odd_code)) = F``;
val _ = observe "even_start_rejects" ``all_enc_ok ^odd_cfg ^labs ^ffis 0 ^odd_code = F``;
