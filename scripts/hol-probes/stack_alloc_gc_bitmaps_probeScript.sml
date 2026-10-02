load "preamble"; load "stack_allocProofTheory";
open bossLib; open HolKernel Parse; open preamble; open stack_allocProofTheory;

val _ = Globals.linewidth := 1000000;
val print_eval = fn label => fn q =>
  (print label; print "="; print (term_to_string (rconc (EVAL q))); print "\n");

val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;
val mem = ``(\a:64 word. if a = 1008w then Word 0x1000000000002w
                          else (Word a : 64 word_loc))``;
val stk = ``[Word 0x101w; Word 4w; Word 7w; Word 9w] : 64 word_loc list``;

val _ = print_eval "gcb_bitmap"
  ``case word_gc_move_bitmap ^conf (13w:64 word, ^stk, 7w, 2000w, 1000w, ^mem, UNIV) of
    | NONE => NONE | SOME (hd,ws,i,pa,m,c) => SOME (hd,ws,i,pa,m 1008w,c)``;
val _ = print_eval "gcb_bitmap_short"
  ``case word_gc_move_bitmap ^conf (13w:64 word, [Word 4w] : 64 word_loc list, 7w, 2000w,
       1000w, ^mem, UNIV) of
    | NONE => NONE | SOME (hd,ws,i,pa,m,c) => SOME (hd,ws,i,pa,c)``;
val _ = print_eval "gcb_bitmaps"
  ``case word_gc_move_bitmaps ^conf (Word (1w:64 word), ^stk, [13w:64 word], 7w, 2000w, 1000w,
       ^mem, UNIV) of
    | NONE => NONE | SOME (hd,ws,i,pa,m,c) => SOME (hd,ws,i,pa,c)``;
val _ = print_eval "gcb_bitmaps_zero"
  ``case word_gc_move_bitmaps ^conf (Word (0w:64 word), ^stk, [13w:64 word], 7w, 2000w, 1000w,
       ^mem, UNIV) of
    | NONE => NONE | SOME (hd,ws,i,pa,m,c) => SOME (hd,ws,i,pa,c)``;
val _ = print_eval "gcb_roots_bitmaps"
  ``let (st,i,pa,m,c) = word_gc_move_roots_bitmaps ^conf
       ([Word 1w; Word 0x101w; Word 4w; Word 7w; Word 0w] : 64 word_loc list, [13w:64 word],
        7w, 2000w, 1000w, ^mem, UNIV) in (st,i,pa,c)``;
