load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val original_pre = Q.prove(`  ∀code enc c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (enc_sec_list enc code)`,
  fs[enc_sec_list_def]>>Induct>>fs[]>>
  Cases>>fs[enc_sec_def]>>rw[]>>
  Induct_on`l`>>fs[]>>Cases>>fs[enc_line_def,line_ok_pre_def]);
val _=capture "all_enc_ok_pre_enc_sec_list" original_pre;
val _=types "all_enc_ok_pre_enc_sec_list_types" original_pre;
val _=print("hypotheses="^Int.toString(length(hyp original_pre))^"\n");
val _=show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((QCONV(SIMP_CONV(srw_ss())[enc_sec_list_def,enc_sec_def,enc_line_def,line_ok_pre_def]) THENC EVAL THENC QCONV(SIMP_CONV(srw_ss())[])) q)); print "\n");
val template = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (128w,127w); hw_offset := (128w,127w); byte_offset := (128w,127w);
 jump_offset := (128w,127w); cjump_offset := (128w,127w); loc_offset := (128w,127w)
 |> : 8 asm_config``;
val _=observe "empty" ``all_enc_ok_pre ^template (enc_sec_list (λa.[1w;2w;3w]) ([]:8 sec list))``;
val _=observe "label" ``all_enc_ok_pre ^template (enc_sec_list (λa.[1w;2w;3w]) ([Section 1 [Label 1 7 99]]:8 sec list))``;
val _=observe "asm_stale" ``all_enc_ok_pre ^template (enc_sec_list (λa.[1w;2w;3w]) ([Section 1 [Asm (Asmi (Inst Skip)) [] 99]]:8 sec list))``;
val _=observe "labasm" ``all_enc_ok_pre ^template (enc_sec_list (λa.[1w;2w;3w]) ([Section 1 [LabAsm (Call (Lab 1 7)) 99w [] 99]]:8 sec list))``;
