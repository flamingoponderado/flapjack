load "preamble"; load "stack_allocProofTheory";
open bossLib; open HolKernel Parse; open preamble; open stack_allocProofTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "get_bits_11" ``get_bits (11w:8 word)``;
val _ = print_eval "get_bits_1" ``get_bits (1w:8 word)``;
val _ = print_eval "get_bits_0" ``get_bits (0w:8 word)``;
val _ = print_eval "get_bits_msb_64" ``get_bits (0x8000000000000005w:64 word)``;
