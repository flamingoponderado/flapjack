load "preamble"; load "stack_allocProofTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val target = ``  !k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'c,'b)stackSem$state).
      word_gen_gc_partial_move_data conf k (ha1,i1,pa1,old1,m1,dm1,gs,rs) =
        (i2,pa2,m2,T) /\
      shift_length conf < dimindex (:'a) /\ word_shift (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ conf.len_size <> 0 /\
      conf.len_size + 2 < dimindex (:'a) /\
      (!w:'a word. w << word_shift (:'a) = w * bytes_in_word) /\
      FLOOKUP s.store CurrHeap = SOME (Word old1) /\ s.use_store /\
      s.memory = m1 /\ s.mdomain = dm1 /\ good_dimindex (:'a) /\
      FLOOKUP s.store (Temp 0w) = SOME (Word gs) /\
      FLOOKUP s.store (Temp 1w) = SOME (Word rs) /\
      0 IN FDOM s.regs /\
      1 IN FDOM s.regs /\
      2 IN FDOM s.regs /\
      get_var 3 s = SOME (Word pa1) /\
      get_var 4 s = SOME (Word (i1:'a word)) /\
      5 IN FDOM s.regs ==>
      6 IN FDOM s.regs ==>
      7 IN FDOM s.regs ==>
      get_var 8 s = SOME (Word ha1) /\ c1 ==>
      ?ck r0 r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_partial_move_data_code conf,s with clock := s.clock + ck) =
          (NONE,s with <| memory := m2;
                          regs := s.regs |++ [(0,r0);
                                              (1,r1);
                                              (2,r2);
                                              (3,Word pa2);
                                              (4,Word i2);
                                              (5,r5);
                                              (6,r6);
                                              (7,r7);
                                              (8,Word pa2)] |>)``;
val _ = print ("partial_data_free_vars=" ^ String.concatWith "," (map (fn v => #1 (dest_var v) ^ ":" ^ type_to_string (type_of v)) (free_vars target)) ^ "\n");
fun walk t =
  if is_var t then let val (n,ty) = dest_var t in
    if n = "t0" then print ("partial_data_t0_type=" ^ type_to_string ty ^ "\n")
    else if n = "t1" then print ("partial_data_t1_type=" ^ type_to_string ty ^ "\n") else () end
  else if is_comb t then let val (f,x) = dest_comb t in walk f; walk x end
  else if is_abs t then let val (v,b) = dest_abs t in walk v; walk b end
  else ();
val _ = walk target;
val _ = Globals.show_types := true;
val _ = print ("partial_data_full_typed_statement=" ^ term_to_string target ^ "\n");

val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;
val print_eval = fn label => fn q =>
  (print (label ^ "="); print (term_to_string (rconc (EVAL q))); print "\n");
val _ = print_eval "partial_data_empty"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 0
      (100w:64 word,7w,100w,1000w,(\a:64 word. Word 4w),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_fuel_zero"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 0
      (100w:64 word,7w,108w,1000w,(\a:64 word. Word 4w),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_skip_zero_length"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 1
      (100w:64 word,7w,108w,1000w,(\a:64 word. Word 4w),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_skip_one_length"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 1
      (100w:64 word,7w,116w,1000w,(\a:64 word. Word 0x1000000000004w),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_pointer_zero_length"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 1
      (100w:64 word,7w,108w,1000w,(\a:64 word. Word 0w),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_pointer_small_field"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 1
      (100w:64 word,7w,116w,1000w,(\a:64 word. Word (if a = 100w then 0x1000000000000w else 4w)),UNIV,8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
val _ = print_eval "partial_data_missing_domain"
  ``let (i,pa,m,c) = word_gen_gc_partial_move_data ^conf 1
      (100w:64 word,7w,108w,1000w,(\a:64 word. Word 4w),{},8w,32w)
    in (i,pa,m 100w,m 108w,m 116w,c)``;
(* No nonword-header concrete oracle: HOL theWord on Loc is unspecified. *)
