load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val enc_lines_again_all_enc_ok_pre = Q.prove (`∀labs ffis pos enc lines acc ok res ok' c.
  enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
  EVERY (line_ok_pre c) lines ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) res`,
  recInduct enc_lines_again_ind>>rw[enc_lines_again_def]>>
  rw[EVERY_REVERSE]>>fs[line_ok_pre_def]);
val _=capture "enc_lines_again_all_enc_ok_pre" enc_lines_again_all_enc_ok_pre;
val _=types "enc_lines_again_all_enc_ok_pre_types" enc_lines_again_all_enc_ok_pre;
val _=print "enc_lines_again_all_enc_ok_pre_hypotheses=";
val _=print(Int.toString(length(hyp enc_lines_again_all_enc_ok_pre)) ^ "\n");
val enc_secs_again_all_enc_ok_pre = Q.prove (`∀pos labs ffis enc ls res ok c.
  enc_secs_again pos labs ffis enc ls = (res,ok) ∧ all_enc_ok_pre c ls ⇒
  all_enc_ok_pre c res`,
  ho_match_mp_tac enc_secs_again_ind>>rw[enc_secs_again_def]>>
  rw[]>>
  rpt (pairarg_tac>>fs[])>>
  rw[]>>
  match_mp_tac enc_lines_again_all_enc_ok_pre>>asm_exists_tac>>fs[]);
val _=capture "enc_secs_again_all_enc_ok_pre" enc_secs_again_all_enc_ok_pre;
val _=types "enc_secs_again_all_enc_ok_pre_types" enc_secs_again_all_enc_ok_pre;
val _=print "enc_secs_again_all_enc_ok_pre_hypotheses=";
val _=print(Int.toString(length(hyp enc_secs_again_all_enc_ok_pre)) ^ "\n");
val line_ok_pre_add_nop = Q.prove (`EVERY (line_ok_pre c) xs ⇒
  EVERY (line_ok_pre c) (add_nop nop xs)`,
  Induct_on`xs`>>EVAL_TAC>>Cases>>fs[]>>rw[]>>EVAL_TAC>>fs[line_ok_pre_def]);
val _=capture "line_ok_pre_add_nop" line_ok_pre_add_nop;
val _=types "line_ok_pre_add_nop_types" line_ok_pre_add_nop;
val _=print "line_ok_pre_add_nop_hypotheses=";
val _=print(Int.toString(length(hyp line_ok_pre_add_nop)) ^ "\n");
val line_ok_pre_pad_section = Q.prove (`∀nop xs acc c.
  EVERY (line_ok_pre c) xs ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (pad_section nop xs acc)`,
  ho_match_mp_tac pad_section_ind>>rw[pad_section_def]>>
  fs[EVERY_REVERSE]>>
  first_x_assum match_mp_tac>>fs[line_ok_pre_def]>>
  metis_tac[line_ok_pre_add_nop]);
val _=capture "line_ok_pre_pad_section" line_ok_pre_pad_section;
val _=types "line_ok_pre_pad_section_types" line_ok_pre_pad_section;
val _=print "line_ok_pre_pad_section_hypotheses=";
val _=print(Int.toString(length(hyp line_ok_pre_pad_section)) ^ "\n");
val all_enc_ok_pre_pad_code = Q.prove (`∀nop code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (pad_code nop code)`,
  ho_match_mp_tac pad_code_ind>>rw[]>>EVAL_TAC>>rw[]>>
  rfs[]>>
  match_mp_tac line_ok_pre_pad_section>>fs[]);
val _=capture "all_enc_ok_pre_pad_code" all_enc_ok_pre_pad_code;
val _=types "all_enc_ok_pre_pad_code_types" all_enc_ok_pre_pad_code;
val _=print "all_enc_ok_pre_pad_code_hypotheses=";
val _=print(Int.toString(length(hyp all_enc_ok_pre_pad_code)) ^ "\n");
val all_enc_ok_pre_lines_upd_lab_len = Q.prove (`∀n lines acc.
  EVERY (line_ok_pre c) lines ∧
  EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))`,
  ho_match_mp_tac lines_upd_lab_len_ind>>rw[lines_upd_lab_len_def]>>
  fs[EVERY_REVERSE,line_ok_pre_def]);
val _=capture "all_enc_ok_pre_lines_upd_lab_len" all_enc_ok_pre_lines_upd_lab_len;
val _=types "all_enc_ok_pre_lines_upd_lab_len_types" all_enc_ok_pre_lines_upd_lab_len;
val _=print "all_enc_ok_pre_lines_upd_lab_len_hypotheses=";
val _=print(Int.toString(length(hyp all_enc_ok_pre_lines_upd_lab_len)) ^ "\n");
val all_enc_ok_pre_upd_lab_len = Q.prove (`∀n code.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (upd_lab_len n code)`,
  ho_match_mp_tac upd_lab_len_ind>>rw[]>> EVAL_TAC>>fs[]>>
  pairarg_tac \\ fs[] \\
  qspecl_then[`n`,`lines`,`[]`]mp_tac all_enc_ok_pre_lines_upd_lab_len
  \\ rw[]);
val _=capture "all_enc_ok_pre_upd_lab_len" all_enc_ok_pre_upd_lab_len;
val _=types "all_enc_ok_pre_upd_lab_len_types" all_enc_ok_pre_upd_lab_len;
val _=print "all_enc_ok_pre_upd_lab_len_hypotheses=";
val _=print(Int.toString(length(hyp all_enc_ok_pre_upd_lab_len)) ^ "\n");
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
val input = ``[Label 1 5 0;Asm (Asmi (Inst Skip)) [0w;0w] 2;LabAsm (Jump (Lab 1 5)) 99w [] 0;Label 1 6 5] : 8 line list``;
val acc = ``[Asm (Asmi (Inst Skip)) [0w] 7] : 8 line list``;
val code = ``[Section 1 ^input;Section 2 []]``;
val _ = observe "encode_lines_false_flag" ``EVERY (line_ok_pre ^cfg) ^input /\ EVERY (line_ok_pre ^cfg) ^acc /\ ~SND(SND(enc_lines_again ^labs ^ffis 4 ^cfg.encode ^input (^acc,T))) /\ EVERY (line_ok_pre ^cfg) (FST(enc_lines_again ^labs ^ffis 4 ^cfg.encode ^input (^acc,T)))``;
val _ = observe "encode_code_false_flag" ``all_enc_ok_pre ^cfg ^code /\ ~SND(enc_secs_again 4 ^labs ^ffis ^cfg.encode ^code) /\ all_enc_ok_pre ^cfg (FST(enc_secs_again 4 ^labs ^ffis ^cfg.encode ^code))``;
val _ = observe "add_nop_actual" ``EVERY (line_ok_pre ^cfg) ^input /\ EVERY (line_ok_pre ^cfg) (add_nop [3w;4w] ^input)``;
val _ = observe "pad_section_actual" ``EVERY (line_ok_pre ^cfg) ^input /\ EVERY (line_ok_pre ^cfg) ^acc /\ EVERY (line_ok_pre ^cfg) (pad_section [3w;4w] ^input ^acc)``;
val _ = observe "pad_code_actual" ``all_enc_ok_pre ^cfg ^code /\ all_enc_ok_pre ^cfg (pad_code [3w;4w] ^code)``;
val _ = observe "update_lines_actual" ``EVERY (line_ok_pre ^cfg) ^input /\ EVERY (line_ok_pre ^cfg) ^acc /\ EVERY (line_ok_pre ^cfg) (FST(lines_upd_lab_len 3 ^input ^acc))``;
val _ = observe "update_code_actual" ``all_enc_ok_pre ^cfg ^code /\ all_enc_ok_pre ^cfg (upd_lab_len 3 ^code)``;
val _ = observe "invalid_accumulator_retained" ``~EVERY (line_ok_pre ^cfg) (pad_section [3w] [] [Asm (Asmi (JumpReg 99)) [] 0])``;
