(* Direct source observations for the StackSem evaluate_def Alloc clause.
   Reference: cakeml/compiler/backend/semantics/stackSemScript.sml:779-783. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val _ = observe "evaluate_alloc_disabled"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      use_alloc := F; stack := [Word 0w]; stack_space := 0;
      regs := FEMPTY |+ (9,Word 10w);
      store := FEMPTY |+ (AllocSize,Word 4w)|>) in
    let (r,s1) = stackSem$evaluate (Alloc 9,s) in
      (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_missing"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      use_alloc := T; stack := [Word 0w]; stack_space := 0;
      regs := FEMPTY; store := FEMPTY |+ (AllocSize,Word 4w)|>) in
    let (r,s1) = stackSem$evaluate (Alloc 9,s) in
      (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_location"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      use_alloc := T; stack := [Word 0w]; stack_space := 0;
      regs := FEMPTY |+ (9,Loc 3 4); store := FEMPTY |+ (AllocSize,Word 4w)|>) in
    let (r,s1) = stackSem$evaluate (Alloc 9,s) in
      (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_word_success"
  ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
      use_alloc := T; stack := [Word 0w]; stack_space := 0; bitmaps := [];
      regs := FEMPTY |+ (9,Word 10w);
      memory := (\a. Word 0w); mdomain := UNIV;
      store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+
        (TriggerGC,Word 20w);
      gc_fun := (\(roots,m,d,st). SOME (roots,m,st))|>) in
    let (r,s1) = stackSem$evaluate (Alloc 9,s) in
      (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_gc_failure" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_alloc := T; stack := [Word 0w]; stack_space := 0; bitmaps := [];
 regs := FEMPTY |+ (9,Word 10w); memory := (λa. Word 0w); mdomain := UNIV;
 store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
 gc_fun := (λ(roots,m,d,st). NONE)|>) in let (r,s1) = stackSem$evaluate (Alloc 9,s) in (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_gc_missing_size" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_alloc := T; stack := [Word 0w]; stack_space := 0; bitmaps := [];
 regs := FEMPTY |+ (9,Word 10w); memory := (λa. Word 0w); mdomain := UNIV;
 store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
 gc_fun := (λ(roots,m,d,st). SOME (roots,m,FEMPTY))|>) in let (r,s1) = stackSem$evaluate (Alloc 9,s) in (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_gc_bad_space" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_alloc := T; stack := [Word 0w]; stack_space := 0; bitmaps := [];
 regs := FEMPTY |+ (9,Word 10w); memory := (λa. Word 0w); mdomain := UNIV;
 store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
 gc_fun := (λ(roots,m,d,st). SOME (roots,m,FEMPTY |+ (AllocSize,Word 10w) |+ (NextFree,Loc 1 2) |+ (TriggerGC,Word 20w)))|>) in let (r,s1) = stackSem$evaluate (Alloc 9,s) in (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;

val _ = observe "evaluate_alloc_gc_exhausted" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 use_alloc := T; stack := [Word 0w]; stack_space := 0; bitmaps := [];
 regs := FEMPTY |+ (9,Word 10w); memory := (λa. Word 0w); mdomain := UNIV;
 store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
 gc_fun := (λ(roots,m,d,st). SOME (roots,m,FEMPTY |+ (AllocSize,Word 30w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w)))|>) in let (r,s1) = stackSem$evaluate (Alloc 9,s) in (r,FLOOKUP s1.regs 9,s1.stack,FLOOKUP s1.store AllocSize)``;
