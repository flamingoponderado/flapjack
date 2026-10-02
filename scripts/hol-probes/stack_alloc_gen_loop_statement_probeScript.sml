load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val target = ``  !k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt (s:('a,'c,'b)stackSem$state).
      word_gen_gc_move_loop conf k (pax,i,pa,ib,pb,pbx,old,m,dm) =
          (i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old) /\ s.use_store /\
      s.memory = m /\ s.mdomain = dm /\
      (tt = 0w <=> pbx = pb /\ pax = pa) /\
      Temp 0w IN FDOM s.store /\
      Temp 1w IN FDOM s.store /\
      Temp 5w IN FDOM s.store /\
      Temp 6w IN FDOM s.store /\
      FLOOKUP s.store (Temp 2w) = SOME (Word pb) /\
      FLOOKUP s.store (Temp 3w) = SOME (Word ib) /\
      FLOOKUP s.store (Temp 4w) = SOME (Word pbx) /\
      0 IN FDOM s.regs /\
      get_var 1 s = SOME (Word pbx) /\
      get_var 2 s = SOME (Word pb) /\
      get_var 3 s = SOME (Word pa) /\
      get_var 4 s = SOME (Word (i:'a word)) /\
      get_var 7 s = SOME (Word tt) /\
      get_var 8 s = SOME (Word pax) /\
      5 IN FDOM s.regs /\
      6 IN FDOM s.regs /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6.
        evaluate (word_gen_gc_move_loop_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m1;
                          store :=
                            s.store |++
                            [(Temp 0w,t0); (Temp 1w,t1); (Temp 2w,Word pb1);
                             (Temp 3w,Word ib1);
                             (Temp 4w,t4); (Temp 5w, t5); (Temp 6w, t6)];
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa1);
                                              (4,Word i1);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,r8)] |>)``;
val _ = Globals.show_types := true;
val _ = print ("gen_loop_full_typed_statement=" ^ term_to_string target ^ "\n");
val _ = print ("gen_loop_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
  has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
  be := F; call_empty_ffi := F; gc_kind := Simple |>``;
val print_eval = fn label => fn q =>
  (print (label ^ "="); print (term_to_string (rconc (EVAL q))); print "\n");
val _ = print_eval "gen_loop_stop"
  ``let (i,pa,ib,pb,m,c) = word_gen_gc_move_loop ^conf 0
    (2000w:64 word,7w,2000w,50w,100w,100w,1000w,(\a:64 word. Word 4w),UNIV)
    in (i,pa,ib,pb,m 100w,m 108w,c)``;
val _ = print_eval "gen_loop_data_fuel_zero"
  ``let (i,pa,ib,pb,m,c) = word_gen_gc_move_loop ^conf 0
    (100w:64 word,7w,108w,50w,3000w,3000w,1000w,(\a:64 word. Word 4w),UNIV)
    in (i,pa,ib,pb,m 100w,m 108w,c)``;
val _ = print_eval "gen_loop_data_one"
  ``let (i,pa,ib,pb,m,c) = word_gen_gc_move_loop ^conf 1
    (100w:64 word,7w,108w,50w,3000w,3000w,1000w,(\a:64 word. Word 4w),UNIV)
    in (i,pa,ib,pb,m 100w,m 108w,c)``;
val _ = print_eval "gen_loop_refs_fuel_zero"
  ``let (i,pa,ib,pb,m,c) = word_gen_gc_move_loop ^conf 0
    (2000w:64 word,7w,2000w,50w,100w,108w,1000w,(\a:64 word. Word 0w),UNIV)
    in (i,pa,ib,pb,m 100w,m 108w,c)``;
val _ = print_eval "gen_loop_refs_one"
  ``let (i,pa,ib,pb,m,c) = word_gen_gc_move_loop ^conf 1
    (2000w:64 word,7w,2000w,50w,100w,108w,1000w,(\a:64 word. Word 0w),UNIV)
    in (i,pa,ib,pb,m 100w,m 108w,c)``;
