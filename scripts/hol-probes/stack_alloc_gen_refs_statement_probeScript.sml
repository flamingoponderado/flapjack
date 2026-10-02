load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val target = ``  !k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_move_refs conf k (r2a1,r1a1,i1,pa1,ib1,pb1,old1,m1,dm1) =
        (r2a2,i2,pa2,ib2,pb2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb1) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib1) /\
      FLOOKUP s.store (Temp 4w) = SOME (Word r1a1) /\
      get_var 0 s = SOME (Word r1a1) /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word r2a1) /\ c1 ==>
      ?ck r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_move_refs_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb2);
                             (Temp 3w,Word ib2)];
                          regs := s.regs |++ [(0,Word r1a1);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word r2a2)] |>)``;
val _ = print ("gen_refs_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
val _ = Globals.show_types := true;
val _ = print ("gen_refs_full_typed_statement=" ^ term_to_string target ^ "\n");
val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;
val print_eval = fn label => fn q =>
  (print (label ^ "="); print (term_to_string (rconc (EVAL q))); print "\n");
val _ = print_eval "gen_refs_empty"
  ``let (re,i,pa,ib,pb,m,c) = word_gen_gc_move_refs ^conf 0
      (100w:64 word,100w,7w,2000w,50w,3000w,1000w,(\a:64 word. Word 4w),UNIV)
    in (re,i,pa,ib,pb,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "gen_refs_fuel_zero"
  ``let (re,i,pa,ib,pb,m,c) = word_gen_gc_move_refs ^conf 0
      (100w:64 word,108w,7w,2000w,50w,3000w,1000w,(\a:64 word. Word 4w),UNIV)
    in (re,i,pa,ib,pb,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "gen_refs_zero_payload"
  ``let (re,i,pa,ib,pb,m,c) = word_gen_gc_move_refs ^conf 1
      (100w:64 word,108w,7w,2000w,50w,3000w,1000w,(\a:64 word. Word 0w),UNIV)
    in (re,i,pa,ib,pb,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "gen_refs_small_field"
  ``let (re,i,pa,ib,pb,m,c) = word_gen_gc_move_refs ^conf 1
      (100w:64 word,116w,7w,2000w,50w,3000w,1000w,(\a:64 word. Word (if a = 100w then 0x1000000000000w else 4w)),UNIV)
    in (re,i,pa,ib,pb,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "gen_refs_missing_domain"
  ``let (re,i,pa,ib,pb,m,c) = word_gen_gc_move_refs ^conf 1
      (100w:64 word,108w,7w,2000w,50w,3000w,1000w,(\a:64 word. Word 0w),{})
    in (re,i,pa,ib,pb,m 100w,m 108w,m 116w,c)``;
