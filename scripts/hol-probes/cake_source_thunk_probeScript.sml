load "semanticPrimitivesTheory";
load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "thunk_op_type="; print_type (type_of ``semanticPrimitives$thunk_op``); print "\n");
val _ = (print "dest_type="; print_type (type_of ``semanticPrimitives$dest_thunk``); print "\n");
val good = rhs (concl (EVAL ``semanticPrimitives$dest_thunk [Loc F 0]
  [Thunk NotEvaluated (Litv (IntLit 1))]``));
val _ = (print "good="; print_term good; print "\n");
val bad = rhs (concl (EVAL ``semanticPrimitives$dest_thunk [Loc T 0]
  [Thunk NotEvaluated (Litv (IntLit 1))]``));
val _ = (print "bad="; print_term bad; print "\n");
val ordinary = rhs (concl (EVAL ``semanticPrimitives$dest_thunk [Loc T 0]
  [Refv (Litv (IntLit 1))]``));
val _ = (print "ordinary="; print_term ordinary; print "\n");
val update = rhs (concl (EVAL ``semanticPrimitives$update_thunk [Loc F 0]
  [Thunk NotEvaluated (Litv (IntLit 1))] [Litv (IntLit 2)]``));
val _ = (print "update="; print_term update; print "\n");
val nested = rhs (concl (EVAL ``semanticPrimitives$update_thunk [Loc F 0]
  [Thunk NotEvaluated (Litv (IntLit 1)); Thunk Evaluated (Litv (IntLit 2))] [Loc F 1]``));
val _ = (print "nested="; print_term nested; print "\n");
val operation = rhs (concl (EVAL ``case (semanticPrimitives$thunk_op
  ([Thunk NotEvaluated (Litv (IntLit 1))], (ARB :unit ffi_state))
  (UpdateThunk Evaluated) [Loc F 0; Litv (IntLit 2)] :
  ((v store # unit ffi_state) # (v,num) result) option) of
    SOME ((s,_),Rval (Conv NONE [])) => SOME s | _ => NONE``));
val _ = (print "operation="; print_term operation; print "\n");
val xor_tail = rhs (concl ((EVAL THENC DEPTH_CONV (CHANGED_CONV wordsLib.WORD_EVAL_CONV))
  ``semanticPrimitives$xor_bytes [3w:word8] [5w; 7w]``));
val _ = (print "xor_tail="; print_term xor_tail; print "\n");
val xor_short = rhs (concl (EVAL ``semanticPrimitives$xor_bytes [3w:word8; 7w] [5w]``));
val _ = (print "xor_short="; print_term xor_short; print "\n");
