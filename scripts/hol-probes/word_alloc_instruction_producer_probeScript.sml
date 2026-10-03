(* Original 16-bit instruction-delta catchall, without changing CakeML. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "gdi_load16_zero"
  ``get_delta_inst (Mem Load16 1 (Addr 2 (0w:64 word)) : 64 inst) = Delta [] []``;
val _ = print_eval "gdi_store16_zero"
  ``get_delta_inst (Mem Store16 1 (Addr 2 (0w:64 word)) : 64 inst) = Delta [] []``;
val _ = print_eval "gdi_load16_offset"
  ``get_delta_inst (Mem Load16 1 (Addr 2 (255w:8 word)) : 8 inst) = Delta [] []``;
val _ = print_eval "gdi_store16_offset"
  ``get_delta_inst (Mem Store16 1 (Addr 2 (255w:8 word)) : 8 inst) = Delta [] []``;
