load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "iv_empty_path" ``parmove$path ([] : (num # num) list)``;
val _ = print_eval "iv_single_path" ``parmove$path [(1:num,2)]``;
val _ = print_eval "iv_chain_path" ``parmove$path [(1:num,2);(2,3);(3,4)]``;
val _ = print_eval "iv_bad_path" ``parmove$path [(1:num,2);(3,4)]``;
val _ = print_eval "iv_empty_wf" ``parmove$wf ([],[],[(NONE,NONE)] : (num option # num option) list)``;
val _ = print_eval "iv_pending_wf" ``parmove$wf ([(SOME (1:num),SOME (2:num));(SOME (3:num),SOME (2:num))],[],[] : (num option # num option) list)``;
val _ = print_eval "iv_repeated" ``parmove$wf ([(SOME (1:num),SOME (2:num));(SOME (1:num),SOME (3:num))],[],[] : (num option # num option) list)``;
val _ = print_eval "iv_pending_dest" ``parmove$wf ([(NONE,SOME (2:num))],[],[] : (num option # num option) list)``;
val _ = print_eval "iv_pending_source" ``parmove$wf ([(SOME (1:num),NONE)],[],[] : (num option # num option) list)``;
val _ = print_eval "iv_active_last_temp" ``parmove$wf ([],[(SOME (1:num),SOME (2:num));(SOME (2:num),NONE)],[] : (num option # num option) list)``;
val _ = print_eval "iv_active_front_temp" ``parmove$wf ([],[(SOME (1:num),NONE);(SOME (2:num),SOME (3:num))],[] : (num option # num option) list)``;
val _ = print_eval "iv_active_dest" ``parmove$wf ([],[(NONE,SOME (2:num))],[] : (num option # num option) list)``;
val _ = print_eval "iv_active_path" ``parmove$wf ([],[(SOME (1:num),SOME (2:num));(SOME (3:num),SOME 4)],[] : (num option # num option) list)``;
