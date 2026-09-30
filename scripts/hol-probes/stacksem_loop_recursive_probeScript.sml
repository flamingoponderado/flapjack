(* Non-stub direct original Loop evaluate observations, stackSemScript.sml:833-837.
   The original total evaluator performs every recursive re-entry. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = observe "continue_three"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 3 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Continue 0), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "skip_three"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 3 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Skip), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "tick_three"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 3 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Tick), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "tick_zero"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 0 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Tick), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "break_zero"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Break 0), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "break_two"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Break 2), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "continue_two"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Continue 2), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "return_location"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Return 4), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "return_word_error"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Return 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "raise_location"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Raise 4), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
val _ = observe "halt_word"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      regs := FEMPTY |+ (1,Word 3w) |+ (4,Loc 4 5);
      stack := [Word 9w]; clock := 5 |>) in
    let (r,s1) = stackSem$evaluate (Loop (Halt 1), s) in
      (r,s1.clock,FLOOKUP s1.regs 1,LENGTH s1.stack)``;
