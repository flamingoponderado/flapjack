(* Original StackProps clock-proof support full statements and variable types.
These source-shape captures do not assert HOL-to-Lean equivalence. *)
load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
  (print_term v; print ":"; print_type(type_of v); print ";")) (free_vars(concl th)); print "\n");
val _ = (print "cp_asm_const_type="; print_type(type_of ``asm$Const``); print "\n");
val _ = (print "cp_clock_neutral_type="; print_type(type_of ``stackProps$clock_neutral``); print "\n");
val _ = capture "cp_1" (DB.fetch "stackProps" "dec_clock_const");
val _ = captureTypes "cp_1_types" (DB.fetch "stackProps" "dec_clock_const");
val _ = capture "cp_2" (DB.fetch "stackProps" "pair_map_eq");
val _ = captureTypes "cp_2_types" (DB.fetch "stackProps" "pair_map_eq");
val _ = capture "cp_3" (DB.fetch "stackProps" "bad_fun_return_IMP");
val _ = captureTypes "cp_3_types" (DB.fetch "stackProps" "bad_fun_return_IMP");
val _ = capture "cp_4" (DB.fetch "stackProps" "cont_loop_IMP");
val _ = captureTypes "cp_4_types" (DB.fetch "stackProps" "cont_loop_IMP");
val _ = capture "cp_5" (DB.fetch "stackProps" "with_clock_ffi");
val _ = captureTypes "cp_5_types" (DB.fetch "stackProps" "with_clock_ffi");
val _ = capture "cp_6" (DB.fetch "stackProps" "clock_neutral_def");
val _ = captureTypes "cp_6_types" (DB.fetch "stackProps" "clock_neutral_def");

fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "cp_skip64" ``clock_neutral (Skip:64 stackLang$prog)``;
val _ = observe "cp_sqrt1" ``clock_neutral (Inst (FP (FPSqrt 0 1)):1 stackLang$prog)``;
val _ = observe "cp_halt16" ``clock_neutral (Halt 2:16 stackLang$prog)``;
val _ = observe "cp_loc1" ``clock_neutral (LocValue 0 1 2:1 stackLang$prog)``;
val _ = observe "cp_seq_good64" ``clock_neutral (Seq Skip (Halt 2):64 stackLang$prog)``;
val _ = observe "cp_seq_tick16" ``clock_neutral (Seq (LocValue 0 1 2) Tick:16 stackLang$prog)``;
val _ = observe "cp_if_good1" ``clock_neutral (If Equal 0 (Reg 1) Skip (Halt 2):1 stackLang$prog)``;
val _ = observe "cp_if_bad64" ``clock_neutral (If Equal 0 (Reg 1) Skip Tick:64 stackLang$prog)``;
val _ = observe "cp_loop_skip64" ``clock_neutral (Loop Skip:64 stackLang$prog)``;
val _ = observe "cp_call_skip1" ``clock_neutral (Call (SOME(Skip,0,1,2)) (INL 3) NONE:1 stackLang$prog)``;
