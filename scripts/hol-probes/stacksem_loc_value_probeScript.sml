(* Original stackSem evaluate_def LocValue961-964; label predicates are proved
   from original loc_check/get_labels rather than assumed by the probe. *)
load "bossLib"; load "preamble"; load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
val leaf = ``LocValue 1 4 5 : 8 stackLang$prog``;
val ret = ``Call (SOME (^leaf,13,4,5)) (INL 0) NONE``;
val handler = ``Call (SOME (^leaf,13,11,12)) (INL 0) (SOME (^leaf,14,15))``;
val noRet = ``Call NONE (INL 0) (SOME (^leaf,14,15))``;
val present = prove (``stackSem$loc_check (insert 3 ^ret LN) (4,5)``,
 rw [loc_check_def] >> qexists_tac `3` >> qexists_tac `^ret` >>
 simp [lookup_insert,get_labels_def]);
val handlerPresent = prove (``stackSem$loc_check (insert 3 ^handler LN) (14,15)``,
 rw [loc_check_def] >> qexists_tac `3` >> qexists_tac `^handler` >>
 simp [lookup_insert,get_labels_def]);
val noRetAbsent = prove (``~stackSem$loc_check (insert 3 ^noRet LN) (14,15)``,
 simp [loc_check_def,lookup_insert,get_labels_def]);
val checks = map (CONV_RULE EVAL) [present,handlerPresent,noRetAbsent];
fun observe label q = let
 val th = CONV_RULE (RAND_CONV EVAL)
   (SIMP_RULE (srw_ss()) checks (EVAL q))
 in print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "loc_zero_present" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := insert 3 ^ret LN; use_stack := T; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 3 0,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "loc_zero_absent" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := LN; use_stack := T; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 3 0,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "loc_nonzero_present" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := insert 3 ^ret LN; use_stack := T; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 4 5,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "loc_handler_present" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := insert 3 ^handler LN; use_stack := T; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 14 15,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "loc_handler_no_return" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := insert 3 ^noRet LN; use_stack := T; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 14 15,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;

val _ = observe "loc_disabled_stack" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 code := insert 3 ^ret LN; use_stack := F; stack := [Word 11w; Loc 3 4];
 stack_space := 1; regs := FEMPTY |+ (7,Word 9w); clock := 17;
 memory := (\a. Word 23w)|>) in
 let (r,s1) = stackSem$evaluate (LocValue 7 4 5,s) in
 (r,FLOOKUP s1.regs 7,s1.stack,s1.stack_space,s1.clock,s1.memory 0w)``;
