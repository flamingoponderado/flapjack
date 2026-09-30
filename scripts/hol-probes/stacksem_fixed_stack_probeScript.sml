(* Original stackSem evaluate_def fixed stack clauses, lines965-1010. *)
load "bossLib"; load "preamble"; load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "stack_alloc_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 1;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackAlloc 1,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_alloc_success" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 2;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackAlloc 1,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_alloc_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 2;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackAlloc 2,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_alloc_exhausted" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 2;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackAlloc 3,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_free_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackFree 2,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_free_excess" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackFree 3,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_free_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackFree 1,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_load_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoad 7 1,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_load_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoad 7 2,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_load_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoad 7 1,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_store_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Loc 5 6); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStore 7 0,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_store_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY; clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStore 7 0,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_store_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStore 7 2,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_store_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStore 7 0,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_size_modular" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 260;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackGetSize 7,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_size_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 260;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackGetSize 7,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "stack_size_unsigned" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack_space := 260; regs := FEMPTY|>) in
 let (r,s1) = stackSem$evaluate (StackGetSize 7,s) in
 (r,OPTION_MAP (\x. case x of Word w => w2n w | Loc label offset => 999) (FLOOKUP s1.regs 7))``;
