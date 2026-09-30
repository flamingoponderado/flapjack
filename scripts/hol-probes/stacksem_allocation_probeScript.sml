(* Direct original stackSem356-400 observations; no oracle implementation. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = observe "space_true" ``stackSem$has_space (Word 10w : 8 word_loc)
  ((FEMPTY |+ (NextFree,(Word 5w : 8 word_loc)) |+ (TriggerGC,Word 20w)))``;
val _ = observe "space_false" ``stackSem$has_space (Word 16w : 8 word_loc)
  ((FEMPTY |+ (NextFree,(Word 5w : 8 word_loc)) |+ (TriggerGC,Word 20w)))``;
val _ = observe "space_wrap" ``stackSem$has_space (Word 250w : 8 word_loc)
  ((FEMPTY |+ (NextFree,(Word 10w : 8 word_loc)) |+ (TriggerGC,Word 4w)))``;
val _ = observe "space_loc" ``stackSem$has_space (Loc 1 0 : 8 word_loc)
  ((FEMPTY |+ (NextFree,(Word 5w : 8 word_loc)) |+ (TriggerGC,Word 20w)))``;
val _ = observe "space_missing" ``stackSem$has_space (Word 0w : 8 word_loc) FEMPTY``;
val _ = observe "space_next_loc" ``stackSem$has_space (Word 0w : 8 word_loc)
  (FEMPTY |+ (NextFree,Loc 1 0) |+ (TriggerGC,Word 20w))``;
val _ = observe "gc_short" ``stackSem$gc
  ((ARB : (8,unit,unit) stackSem$state) with <|stack := []; stack_space := 1|>)``;
val _ = observe "gc_bad_stack" ``stackSem$gc
  ((ARB : (8,unit,unit) stackSem$state) with <|stack := []; stack_space := 0; bitmaps := []|>)``;
val _ = observe "gc_none" ``stackSem$gc
  ((ARB : (8,unit,unit) stackSem$state) with <|stack := [Word 0w]; stack_space := 0;
    bitmaps := []; gc_fun := (λx. NONE)|>)``;
val _ = observe "gc_decode_fail" ``stackSem$gc
  ((ARB : (8,unit,unit) stackSem$state) with <|stack := [Word 0w]; stack_space := 0;
    bitmaps := []; gc_fun := (λ(wl,m,d,st). SOME ([Word 1w],m,st))|>)``;
val _ = observe "gc_success" ``OPTION_MAP (λs. (s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w))
  (stackSem$gc ((ARB : (8,unit,unit) stackSem$state) with
   <|stack := [Word 99w; Word 1w;Word 7w;Word 0w];stack_space := 1;bitmaps := [3w];
     regs := FEMPTY |+ (9,Word 2w); memory := (λa. Word 0w); mdomain := UNIV;
     store := FEMPTY |+ (AllocSize,Word 4w);
     gc_fun := (λ(wl,m,d,st). SOME ([Word 9w],(λa. Word 8w),st |+ (AllocSize,Word 5w)))|>))``;
val _ = observe "space_mixed" ``stackSem$has_space (Word 1w : 1 word_loc)
  ((FEMPTY |+ (NextFree,(Word 5w : 8 word_loc)) |+ (TriggerGC,Word 20w)))``;
val _ = print "type_space=";
val _ = print_type (type_of ``stackSem$has_space``);
val _ = print "\n";
val _ = observe "alloc_success" ``let (r,s) = stackSem$alloc 10w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λ(wl,m,d,st). SOME (wl,m,st))|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
val _ = observe "alloc_halt" ``let (r,s) = stackSem$alloc 16w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λ(wl,m,d,st). SOME (wl,m,st))|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
val _ = observe "alloc_gc_failure" ``let (r,s) = stackSem$alloc 10w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λx. NONE)|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
val _ = observe "alloc_missing" ``let (r,s) = stackSem$alloc 10w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λ(wl,m,d,st). SOME (wl,m,FEMPTY))|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
val _ = observe "alloc_bad_amount" ``let (r,s) = stackSem$alloc 10w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λ(wl,m,d,st). SOME (wl,m,st |+ (AllocSize,Loc 1 0)))|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
val _ = observe "alloc_bad_space" ``let (r,s) = stackSem$alloc 10w ((ARB : (8,unit,unit) stackSem$state) with
 <|stack := [Word 0w];stack_space := 0;bitmaps := [];
   regs := FEMPTY |+ (9,Word 2w);memory := (λa. Word 0w);mdomain := UNIV;
   store := FEMPTY |+ (AllocSize,Word 4w) |+ (NextFree,Word 5w) |+ (TriggerGC,Word 20w);
   gc_fun := (λ(wl,m,d,st). SOME (wl,m,FEMPTY |+ (AllocSize,Word 10w) |+ (TriggerGC,Word 20w)))|>) in
 (r,s.stack,FLOOKUP s.regs 9,FLOOKUP s.store AllocSize,s.memory 0w)``;
