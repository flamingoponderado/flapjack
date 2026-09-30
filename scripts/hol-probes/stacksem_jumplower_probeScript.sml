(* Direct source observations for the StackSem evaluate_def JumpLower clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:838-849. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

(* A shared code map: 10 -> Return 4, 12 -> Break 2, 13 -> Continue 3,
   14 -> Skip.  Register 4 holds Loc 4 5, so the recursive sub-evaluations
   terminate on a single unfold. *)

val _ = observe "jump_lower_success"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) (insert 12 (Break 2)
        (insert 13 (Continue 3) (insert 14 Skip LN)));
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_timeout"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) (insert 12 (Break 2)
        (insert 13 (Continue 3) (insert 14 Skip LN)));
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_code_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 11,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_comparison_false"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 2 1 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_loc_operand"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 4 2 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_break_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 12 (Break 2) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 12,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_continue_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 13 (Continue 3) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 13,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "jump_lower_none_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (2,Word 7w) |+ (4,Loc 4 5);
      code := insert 14 Skip LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (JumpLower 1 2 14,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
