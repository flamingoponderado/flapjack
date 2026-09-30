(* Original StackSem seven leaf evaluation clauses. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = observe "skip" ``let (r,s) = stackSem$evaluate (stackLang$Skip,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "halt_word" ``let (r,s) = stackSem$evaluate (stackLang$Halt 1,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "halt_loc" ``let (r,s) = stackSem$evaluate (stackLang$Halt 2,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "halt_missing" ``let (r,s) = stackSem$evaluate (stackLang$Halt 3,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "tick_zero" ``let (r,s) = stackSem$evaluate (stackLang$Tick,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 0|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "tick_one" ``let (r,s) = stackSem$evaluate (stackLang$Tick,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "return_loc" ``let (r,s) = stackSem$evaluate (stackLang$Return 2,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "return_word" ``let (r,s) = stackSem$evaluate (stackLang$Return 1,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "return_missing" ``let (r,s) = stackSem$evaluate (stackLang$Return 3,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "raise_loc" ``let (r,s) = stackSem$evaluate (stackLang$Raise 2,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "raise_word" ``let (r,s) = stackSem$evaluate (stackLang$Raise 1,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "raise_missing" ``let (r,s) = stackSem$evaluate (stackLang$Raise 3,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "break_zero" ``let (r,s) = stackSem$evaluate (stackLang$Break 0,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "break_three" ``let (r,s) = stackSem$evaluate (stackLang$Break 3,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "continue_zero" ``let (r,s) = stackSem$evaluate (stackLang$Continue 0,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
val _ = observe "continue_three" ``let (r,s) = stackSem$evaluate (stackLang$Continue 3,((ARB : (8,unit,unit) stackSem$state) with <|regs := FEMPTY |+ (1,Word 7w) |+ (2,Loc 4 5);stack := [Word 9w];clock := 1|>)) in (r,s.clock,LENGTH s.stack,FLOOKUP s.regs 1)``;
