(* Direct source observations for the StackSem evaluate_def structured-control
   clauses Seq, If, and Loop.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:811-837.
   STOP is the identity abbreviation (stackSemScript.sml:663-664), so the Loop
   reentry call is on Loop c1 itself with the decremented clock. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Shared fixture: register 1 holds Word 3w, register 4 holds Loc 4 5, the
   stack holds one word. The code map is empty because these clauses never
   perform a code lookup. Each row sets its own clock. *)

val _ = observe "seq_normal"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Seq (Return 4) (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "seq_fallthrough"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Seq Skip (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "seq_tick_clamp"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Seq Tick (Return 4), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "if_true"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (If Equal 1 (Imm 3w) (Return 4) (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "if_false"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (If Equal 1 (Imm 4w) (Return 4) (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "if_cmp_none"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (If Equal 4 (Imm 3w) (Return 4) (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "if_operand_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (If Equal 9 (Imm 3w) (Return 4) (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "loop_recurse"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 1 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Continue 0), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "loop_timeout"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (Loop Skip, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "loop_exit_break"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Break 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "loop_exit_continue"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Continue 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
