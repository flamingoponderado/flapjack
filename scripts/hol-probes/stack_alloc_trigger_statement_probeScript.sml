load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val target = ``
    evaluate (SetNewTrigger endh_reg ib_reg gen_sizes,s5) = (res,new_s) ==>
    !ib endh w.
      good_dimindex (:'a) /\ s5.use_store /\
      ALL_DISTINCT [1; 4; 7; ib_reg; endh_reg] /\
      FLOOKUP s5.regs ib_reg = SOME (Word ib) /\
      FLOOKUP s5.regs endh_reg = SOME (Word endh) /\
      FLOOKUP s5.store AllocSize = SOME (Word (w:'a word)) ==>
      ?r7 r1 r4.
        res = NONE /\
        new_s = s5 with <| regs := s5.regs |+ (1,r1) |+ (7,r7) |+ (4,r4);
                           store := s5.store |+ (TriggerGC,
                             Word ((ib + new_trig (endh - ib) w gen_sizes))) |>``;
val _ = Globals.show_types := true;
val _ = print ("trigger_full_typed_statement=" ^ term_to_string target ^ "\n");
val _ = print ("trigger_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
val print_eval = fn label => fn q =>
  (print (label ^ "="); print (term_to_string (rconc (EVAL q))); print "\n");
val _ = print_eval "trigger_generation_cap" ``new_trig (1000w:word64) 16w [4]``;
val _ = print_eval "trigger_heap_cap" ``new_trig (24w:word64) 16w [4]``;
val _ = print_eval "trigger_alloc_exceeds_heap" ``new_trig (24w:word64) 64w [4]``;
val _ = print_eval "trigger_aligned_alloc" ``new_trig (1000w:word64) 64w [4]``;
val _ = print_eval "trigger_unaligned_alloc" ``new_trig (1000w:word64) 65w [4]``;
val _ = print_eval "trigger_32_aligned_alloc" ``new_trig (1000w:word32) 20w [4]``;
val _ = print_eval "trigger_32_unaligned_alloc" ``new_trig (1000w:word32) 21w [4]``;
val _ = print_eval "trigger_run_generation_cap"
  ``let s = (ARB : (64,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 1100w);
       store := FEMPTY |+ (AllocSize,Word 16w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_heap_cap"
  ``let s = (ARB : (64,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 124w);
       store := FEMPTY |+ (AllocSize,Word 16w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_alloc_exceeds_heap"
  ``let s = (ARB : (64,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 124w);
       store := FEMPTY |+ (AllocSize,Word 64w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_aligned_alloc"
  ``let s = (ARB : (64,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 1100w);
       store := FEMPTY |+ (AllocSize,Word 64w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_unaligned_alloc"
  ``let s = (ARB : (64,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 1100w);
       store := FEMPTY |+ (AllocSize,Word 65w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_32_aligned_alloc"
  ``let s = (ARB : (32,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 1100w);
       store := FEMPTY |+ (AllocSize,Word 20w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
val _ = print_eval "trigger_run_32_unaligned_alloc"
  ``let s = (ARB : (32,unit,unit) stackSem$state) with <|
       regs := FEMPTY |+ (0,Word 42w) |+ (3,Word 100w) |+ (8,Word 1100w);
       store := FEMPTY |+ (AllocSize,Word 21w) |+ (CurrHeap,Word 9w);
       use_store := T; clock := 6 |>
     in let (r,t) = stackSem$evaluate (SetNewTrigger 8 3 [4],s)
     in (r,FLOOKUP t.regs 1,FLOOKUP t.regs 7,FLOOKUP t.regs 4,
       FLOOKUP t.store TriggerGC,t.clock,FLOOKUP t.regs 0,
       FLOOKUP t.regs 3,FLOOKUP t.regs 8,FLOOKUP t.store CurrHeap)``;
