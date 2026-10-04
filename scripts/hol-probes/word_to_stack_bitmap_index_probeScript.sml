load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;
val _ = Feedback.set_trace "types" 1;
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
(* Original wLive's index is an n2w word payload, without a stored-count bound.
   Keep complete program/state outcomes at wrapping and bypass boundaries. *)
val _ = out "index_width1_wrap" ``wLive (LN,LN) (List [4w],1) (22,2,1) : 1 stackLang$prog # (1 word app_list # num)``;
val _ = out "index_width8_wrap" ``wLive (LN,LN) (List [4w],255) (22,2,1) : 8 stackLang$prog # (8 word app_list # num)``;
val _ = out "index_width8_below" ``wLive (LN,LN) (List [4w],254) (22,2,1) : 8 stackLang$prog # (8 word app_list # num)``;
val _ = out "index_empty_frame" ``wLive (LN,LN) (List [4w],255) (22,0,1) : 8 stackLang$prog # (8 word app_list # num)``;
