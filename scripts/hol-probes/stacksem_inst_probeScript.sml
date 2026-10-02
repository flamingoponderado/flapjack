(* Direct source observations for the StackSem evaluate_def Inst clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:789-792. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val st = ``((ARB : (64,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 9w) |+ (2,Word 5w) |+ (4,Loc 3 0);
      memory := (\a. Word a); mdomain := {}; be := F; clock := 6 |>)``;

val _ = observe "inst_const"
  ``let (r,s1) = stackSem$evaluate (Inst (Const 1 7w), ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
val _ = observe "inst_add_imm"
  ``let (r,s1) = stackSem$evaluate (Inst (Arith (Binop Add 1 2 (Imm 1w))), ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
val _ = observe "inst_add_missing_reg"
  ``let (r,s1) = stackSem$evaluate (Inst (Arith (Binop Add 1 2 (Reg 3))), ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
val _ = observe "inst_add_loc"
  ``let (r,s1) = stackSem$evaluate (Inst (Arith (Binop Add 1 4 (Imm 1w))), ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
val _ = observe "inst_load_outside"
  ``let (r,s1) = stackSem$evaluate (Inst (Mem Load 1 (Addr 2 0w)), ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
val _ = observe "inst_skip"
  ``let (r,s1) = stackSem$evaluate (Inst Skip, ^st) in
      (r, FLOOKUP s1.regs 1, s1.clock)``;
