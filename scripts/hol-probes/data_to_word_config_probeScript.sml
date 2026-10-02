load "preamble"; load "data_to_wordTheory";
open bossLib; open HolKernel Parse; open preamble; open data_to_wordTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val conf = ``<| tag_bits := 1; len_bits := 2; pad_bits := 3; len_size := 16;
               has_div := F; has_longdiv := F; has_fp_ops := F; has_fp_tern := F;
               be := F; call_empty_ffi := F; gc_kind := Simple |>``;

val _ = print_eval "shift_length" ``shift_length ^conf``;
val _ = print_eval "small_shift_length" ``small_shift_length ^conf``;
val _ = print_eval "gen_size_nil_64" ``(get_gen_size [] : 64 word)``;
val _ = print_eval "gen_size_ten_64" ``(get_gen_size [10; 20] : 64 word)``;
val _ = print_eval "gen_size_overflow_64" ``(get_gen_size [2305843009213693952] : 64 word)``;
val _ = print_eval "gen_size_three_32" ``(get_gen_size [3] : 32 word)``;
