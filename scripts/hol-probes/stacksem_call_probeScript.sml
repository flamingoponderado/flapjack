(* Direct source observations for the StackSem evaluate_def Call clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:861-892. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

(* Register 1 holds the observed Word 3w; register 4 holds Loc 4 5, register 5
   holds Loc 6 7, and link register 3 receives the return Loc. Code entries:
   10 -> Return 4 (successful result), 12 -> Break 2, 13 -> Continue 2,
   14 -> Raise 5 (successful exception), 15 -> Skip (none). Label 20 is absent. *)

val _ = observe "call_tail_success"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call NONE (INL 10) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_tail_handler_error"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call NONE (INL 10) (SOME (Skip,0,0)), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_tail_code_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call NONE (INL 20) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_tail_timeout"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (Call NONE (INL 10) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_success"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 10) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_success_handler"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 10) (SOME (Return 4,6,7)), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_wrong_loc"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,6,7)) (INL 10) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_code_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 20) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_timeout"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Return 4) LN;
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 10) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_exception_handled"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5) |+ (5,Loc 6 7);
      code := insert 14 (Raise 5) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 14) (SOME (Return 4,6,7)), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_exception_unhandled"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5) |+ (5,Loc 6 7);
      code := insert 14 (Raise 5) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 14) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_exception_wrong_loc"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5) |+ (5,Loc 6 7);
      code := insert 14 (Raise 5) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 14) (SOME (Return 4,8,9)), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_break"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 12 (Break 2) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 12) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "call_return_continue"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 13 (Continue 2) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Call (SOME (Return 4,3,4,5)) (INL 13) NONE, s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
