load "bossLib";
load "preamble";
load "stack_to_labProofTheory";
open bossLib HolKernel Parse preamble stack_to_labTheory stackPropsTheory
 labPropsTheory lab_to_targetTheory asmTheory miscTheory;
val _ = Globals.linewidth := 10000;
val original_flatten_line_ok_pre = prove (``∀t p n m cs bs ls a b c.
  byte_offset_ok c 0w /\
  stack_asm_ok c p ∧
  flatten t p n m cs bs = (ls,a,b) ⇒
  EVERY (line_ok_pre c) (append ls)``,
  ho_match_mp_tac flatten_ind>>Cases_on`p`>>rw[]>>
  pop_assum mp_tac>>simp[Once flatten_def]>>rw[]>>fs[]
  >-
    (EVAL_TAC>>fs[stack_asm_ok_def])
  >-
    (every_case_tac>>fs[stack_asm_ok_def]>>
    rpt(pairarg_tac>>fs[])>>
    Cases_on`s`>>fs[]>>rw[]>>TRY(EVAL_TAC>>fs[]>>NO_TAC))
  >-
    (rpt(pairarg_tac>>fs[CaseEq"bool"])>>fs[stack_asm_ok_def]>>
    rw[] \\ EVAL_TAC)
  >-
    (*TODO: Actually the jump part of Ifs should be moved out into the
    line_ok_pre check as well as well *)
    (rpt(pairarg_tac>>fs[])>>
    every_case_tac>>fs[stack_asm_ok_def]>>rw[]>>EVAL_TAC)
  >-
    (*TODO: see above*)
    (rpt(pairarg_tac>>fs[])>>rw[]>>fs[stack_asm_ok_def]>>
    EVAL_TAC)
  >>
    pop_assum mp_tac>>EVAL_TAC>>
    pop_assum mp_tac>>EVAL_TAC>>
    fs[]>>
    Cases_on ‘a’>>EVAL_TAC>>rw[]
);
val _ = print ("full_flatten_source_proof=" ^ term_to_string (concl original_flatten_line_ok_pre) ^ "\n");

val cfg = ``<| ISA := RISC_V ;
              encode := (\x. ([] : word8 list)) ;
              big_endian := F ;
              code_alignment := 2 ;
              link_reg := NONE ;
              avoid_regs := [3] ;
              reg_count := 8 ;
              fp_reg_count := 4 ;
              two_reg_arith := T ;
              valid_imm := (K (K T)) ;
              addr_offset := (0w, 100w) ;
              hw_offset := (0w, 100w) ;
              byte_offset := (0w, 100w) ;
              jump_offset := (0w, 100w) ;
              cjump_offset := (0w, 100w) ;
              loc_offset := (0w, 100w) |> : 8 asm_config``;
val _ = print ("full_compile_all_source_statement=" ^ thm_to_string stack_to_labProofTheory.compile_all_enc_ok_pre ^ "\n");
val programs = ``[(7, Seq (CodeBufferWrite 1 2) Tick); (8, Loop (Break 0)); (9, If Less 3 (Reg 4) Tick Skip); (10, Call (SOME (Tick,3,8,9)) (INR 4) (SOME (Tick,10,11)))] : (num # 8 stackLang$prog) list``;
val _ = print ("full_compile_all_application=" ^ term_to_string (rconc (EVAL ``(byte_offset_ok ^cfg 0w, EVERY (λ(n,p). stack_asm_ok ^cfg p) ^programs, all_enc_ok_pre ^cfg (MAP prog_to_section ^programs))``)) ^ "\n");
val _ = print ("full_compile_all_sections=" ^ term_to_string (rconc (EVAL ``MAP prog_to_section ^programs``)) ^ "\n");
