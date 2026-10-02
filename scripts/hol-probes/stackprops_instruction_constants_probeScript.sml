(* Complete original StackProps instruction constants/commutation source
statements and full types. Local theorems are re-proved verbatim from source,
not claimed to be exported theory bindings. No HOL-to-Lean equivalence claim. *)
load "bossLib";
load "preamble";
load "stackPropsTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory machine_ieeeTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_abs_def, fp64_negate_def];
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
  print (term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
  (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val inst_clock_neutral_source = prove (``(inst i s = SOME t ==> inst i (s with clock := k) = SOME (t with clock := k)) /\
    (inst i s = NONE ==> inst i (s with clock := k) = NONE)``,
Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,set_fp_var_def]
  \\ srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality]);
val inst_clock_neutral_ffi_source = prove (``(inst i s = SOME t ==> inst i (s with ffi := k) = SOME (t with ffi := k)) /\
    (inst i s = NONE ==> inst i (s with ffi := k) = NONE)``,
Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,state_component_equality,set_fp_var_def]>>
  reverse full_case_tac>>fs[]>>
  TRY
    (qmatch_goalsub_abbrev_tac`get_vars _ _`>>
    fs[get_vars_def,get_var_def]>>
    rpt (BasicProvers.TOP_CASE_TAC>>fs[state_component_equality]))
  \\ rpt (srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality]));
val _ = capture "ic_fields" (DB.fetch "stackProps" "inst_const");
val _ = captureTypes "ic_fields_types" (DB.fetch "stackProps" "inst_const");
val _ = capture "ic_map" (DB.fetch "stackProps" "inst_with_const");
val _ = captureTypes "ic_map_types" (DB.fetch "stackProps" "inst_with_const");
val _ = capture "ic_clock" inst_clock_neutral_source;
val _ = captureTypes "ic_clock_types" inst_clock_neutral_source;
val _ = capture "ic_ffi" inst_clock_neutral_ffi_source;
val _ = captureTypes "ic_ffi_types" inst_clock_neutral_ffi_source;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = show_types := false;
val _ = observe "ic_const_clock" ``OPTION_MAP (λt. (t.clock,FLOOKUP t.regs 1)) (stackSem$inst (asm$Const 1 12w) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>))``;
val _ = observe "ic_const_clock_zero" ``OPTION_MAP (λt. (t.clock,FLOOKUP t.regs 1)) (stackSem$inst (asm$Const 1 12w) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with clock := 0))``;
val _ = observe "ic_div_failure" ``OPTION_MAP (λt. t.clock) (stackSem$inst (Arith (Div 1 1 3)) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with clock := 0))``;
val _ = observe "ic_or_location" ``OPTION_MAP (λt. (t.clock,FLOOKUP t.regs 1)) (stackSem$inst (Arith (Binop Or 1 2 (Reg 2))) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>))``;
val _ = observe "ic_store_success" ``OPTION_MAP (λt. (t.clock,t.memory 0w)) (stackSem$inst (Mem Store 2 (Addr 1 0w)) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with regs := FEMPTY |+ (1,Word 0w) |+ (2,Loc 4 5)))``;
val _ = observe "ic_store_failure" ``OPTION_MAP (λt. t.clock) (stackSem$inst (Mem Store 2 (Addr 1 0w)) ((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>))``;
val _ = observe "ic_fp_abs" ``OPTION_MAP (λt. (t.clock,FLOOKUP t.fp_regs 1)) (stackSem$inst (FP (FPAbs 1 0)) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with clock := 0))``;
val _ = observe "ic_fp_missing" ``OPTION_MAP (λt. t.clock) (stackSem$inst (FP (FPMov 1 3)) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with clock := 0))``;
val _ = observe "ic_const_ffi" ``OPTION_MAP (λt. (t.ffi = k,t.clock,FLOOKUP t.regs 1)) (stackSem$inst (asm$Const 1 12w) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with ffi := k))``;
val _ = observe "ic_none_ffi" ``OPTION_MAP (λt. t.ffi = k) (stackSem$inst (FP (FPMov 1 3)) (((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);fp_regs := FEMPTY |+ (0,0xBFF0000000000000w);store := FEMPTY;memory := (λa. Word 11w);mdomain := {0w};clock := 19|>) with ffi := k))``;
