(* Direct original stackSem evaluate Call INR/link-register observations.
   Source: stackSemScript.sml find_code645-651 and returning Call861-892.
   Code and continuations are actual Return leaves, not a replacement evaluator.
   Result, clock, link register3, target register4, stack length are observed.
   An INR3/link3 alias must fail before the return location is written. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;
val base = ``((ARB : (8,unit,unit) stackSem$state) with <|
  regs := FEMPTY |+ (1,Word 3w) |+ (3,Loc 10 0) |+ (4,Loc 10 0);
  code := insert 10 (Return 3) LN;
  stack := [Word 9w]; clock := 5 |>)``;
val proj = ``\(rs:8 stackSem$result option # (8,unit,unit) stackSem$state).
  let (r,s) = rs in (r,s.clock,FLOOKUP s.regs 3,FLOOKUP s.regs 4,LENGTH s.stack)``;
val _ = observe "indirect_tail"
  ``^proj (stackSem$evaluate (Call (NONE) (INR 4) NONE, ^base))``;
val _ = observe "indirect_return"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, ^base))``;
val _ = observe "indirect_link_alias"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 3) NONE, ^base))``;
val _ = observe "indirect_tail_alias"
  ``^proj (stackSem$evaluate (Call (NONE) (INR 3) NONE, ^base))``;
val _ = observe "indirect_nonzero"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with regs := (^base).regs |+ (4,Loc 10 1))))``;
val _ = observe "indirect_word"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with regs := (^base).regs |+ (4,Word 10w))))``;
val _ = observe "indirect_missing"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with regs := (^base).regs \\ 4)))``;
val _ = observe "indirect_code_missing"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with regs := (^base).regs |+ (4,Loc 20 0))))``;
val _ = observe "indirect_timeout"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with clock := 0)))``;
val _ = observe "indirect_wrong_return"
  ``^proj (stackSem$evaluate (Call (SOME (Return 3,3,7,8)) (INR 4) NONE, (^base with code := insert 10 (Return 4) LN)))``;
