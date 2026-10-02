load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val target = ``
   alloc w (s:('a,'c,'b)stackSem$state) = (r,t) /\ r <> SOME Error /\
    s.gc_fun = word_gc_fun conf /\ conf.gc_kind = Generational gen_sizes /\
    LENGTH s.bitmaps < dimword (:'a) - 1 /\
    LENGTH s.stack * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (Word w) ==>
    ?ck l2.
      evaluate
        (word_gc_code conf,
         s with
           <| use_store := T; use_stack := T; use_alloc := F;
              clock := s.clock + ck; regs := l; gc_fun := anything;
              code := fromAList (stack_alloc$compile c (toAList s.code))|>) =
        (r,
         t with
           <| use_store := T; use_stack := T; use_alloc := F;
              code := fromAList (stack_alloc$compile c (toAList s.code));
              regs := l2; gc_fun := anything |>) /\
       (r <> NONE ==> r = SOME (Halt (Word 1w))) /\
       t.regs SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret)``;
val _ = print ("gen_alloc_typed_statement=" ^ term_to_string target ^ "\n");
val _ = print ("gen_alloc_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
