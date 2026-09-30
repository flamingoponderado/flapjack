(* Direct source observations for the StackSem evaluate_def RawCall clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:849-861. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

(* Code entries: 10 -> Seq Skip (Return 4) exercises the successful body;
   12 -> Skip and 13 -> Seq Skip (Break 2) / 14 -> Seq Skip (Continue 3)
   exercise the non-Seq and bad-return paths. Register 4 holds Loc 4 5. *)

val _ = observe "raw_call_success"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Seq Skip (Return 4)) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_timeout"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Seq Skip (Return 4)) LN;
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 10,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_code_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 10 (Seq Skip (Return 4)) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 11,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_non_seq"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 12 Skip LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 12,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_break_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 13 (Seq Skip (Break 2)) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 13,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_continue_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 14 (Seq Skip (Continue 3)) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 14,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;

val _ = observe "raw_call_none_sub"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      code := insert 15 (Seq Skip Skip) LN;
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (RawCall 15,s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
