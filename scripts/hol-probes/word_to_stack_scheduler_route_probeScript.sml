load "bossLib";
load "preamble";
load "parmoveTheory";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble parmoveTheory word_to_stackTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "sr_order_empty" ``parmove$parmove ([] : (num # num) list)``;
val _ = print_eval "sr_order_swap" ``parmove$parmove [(0:num,1);(1,0)]``;
val _ = print_eval "sr_order_duplicate" ``parmove$parmove [(0:num,1);(0,2)]``;
val _ = print_eval "sr_none_slot" ``word_to_stack$format_var 22 NONE``;
val _ = print_eval "sr_spill_cycle" ``word_to_stack$wMove [(44,46);(46,44)] (22,3,2) : 64 word stackLang$prog``;
val _ = print_eval "sr_spill_zero_frame" ``word_to_stack$wMove [(44,46);(46,44)] (22,0,0) : 64 word stackLang$prog``;
