(* Original stackSem evaluate_def dynamic-index clauses978-1007. *)
load "bossLib"; load "preamble"; load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "any_load_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w) |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_alias" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 7,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY; clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_offset_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Loc 3 4); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_unaligned" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 16w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_space" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 1;
 regs := FEMPTY |+ (8,Word 0w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Loc 5 6) |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_alias" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 7,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_offset_missing" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_offset_loc" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w) |+ (8,Loc 3 4); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_unaligned" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w) |+ (8,Word 9w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_boundary" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w) |+ (8,Word 16w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_store_disabled" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_stack := F; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (7,Word 9w) |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackStoreAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_width32" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 4w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_width64" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 8w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_width1_zero" ``let s = ((ARB : (1,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 0w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "any_load_width1_nonzero" ``let s = ((ARB : (1,unit,unit) stackSem$state) with <|
 use_stack := T; stack := [Word 11w; Loc 3 4]; stack_space := 0;
 regs := FEMPTY |+ (8,Word 1w); clock := 17; memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (StackLoadAny 7 8,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

