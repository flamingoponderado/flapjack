load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "closure_type="; print_type (type_of ``semanticPrimitives$Closure``); print "\n");
val _ = (print "recclosure_type="; print_type (type_of ``semanticPrimitives$Recclosure``); print "\n");
val _ = (print "store_assign_type="; print_type (type_of ``semanticPrimitives$store_assign``); print "\n");
val _ = (print "compiler_type="; print_type (type_of ``λ(s:semanticPrimitives$eval_decs_state). s.compiler``); print "\n");
val _ = (print "oracle_type="; print_type (type_of ``λ(s:semanticPrimitives$eval_oracle_state). s.custom_do_eval``); print "\n");
val _ = (print "state_ffi_type="; print_type (type_of ``λ(s:'ffi semanticPrimitives$state). s.ffi``); print "\n");
val _ = (print "state_eval_type="; print_type (type_of ``λ(s:'ffi semanticPrimitives$state). s.eval_state``); print "\n");
val ref_same = rhs (concl (EVAL ``semanticPrimitives$store_v_same_type (Refv (1:num)) (Refv 2)``));
val _ = (print "ref_same="; print_term ref_same; print "\n");
val thunk_update = rhs (concl (EVAL ``semanticPrimitives$store_v_same_type
  (Thunk NotEvaluated (1:num)) (Thunk Evaluated 2)``));
val _ = (print "thunk_update="; print_term thunk_update; print "\n");
val thunk_final = rhs (concl (EVAL ``semanticPrimitives$store_v_same_type
  (Thunk Evaluated (1:num)) (Thunk NotEvaluated 2)``));
val _ = (print "thunk_final="; print_term thunk_final; print "\n");
val allocation = rhs (concl (EVAL ``semanticPrimitives$store_alloc (Refv (7:num)) [Refv 3]``));
val _ = (print "allocation="; print_term allocation; print "\n");
val lookup = rhs (concl (EVAL ``semanticPrimitives$store_lookup 0 [Refv (3:num)]``));
val _ = (print "lookup="; print_term lookup; print "\n");
val update = rhs (concl (EVAL ``semanticPrimitives$store_assign 0 (Refv (7:num)) [Refv 3]``));
val _ = (print "update="; print_term update; print "\n");
val invalid = rhs (concl (EVAL ``semanticPrimitives$store_assign 1 (Refv (7:num)) [Refv 3]``));
val _ = (print "invalid="; print_term invalid; print "\n");
val wrong_type = rhs (concl (EVAL ``semanticPrimitives$store_assign 0 (Varray [7:num]) [Refv 3]``));
val _ = (print "wrong_type="; print_term wrong_type; print "\n");
