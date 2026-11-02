load "semanticsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "evaluate_type="; print_type (type_of ``semantics$evaluate_prog_with_clock``); print "\n");
val _ = (print "semantics_type="; print_type (type_of ``semantics$semantics_prog``); print "\n");
val _ = (print "evaluate_definition="; print_thm semanticsTheory.evaluate_prog_with_clock_def; print "\n");
val _ = (print "semantics_definition="; print_thm semanticsTheory.semantics_prog_def; print "\n");
val empty = prove (``∀(st:'ffi semanticPrimitives$state) env.
  semantics$semantics_prog st env [] (Terminate Success st.ffi.io_events)``,
  simp [semanticsTheory.semantics_prog_def, semanticsTheory.evaluate_prog_with_clock_def,
        evaluateTheory.evaluate_decs_def]);
val _ = (print "empty_terminates="; print_thm empty; print "\n");
val empty_iff = prove (``∀(st:'ffi semanticPrimitives$state) env beh.
  semantics$semantics_prog st env [] beh ⇔ beh = Terminate Success st.ffi.io_events``,
  rpt gen_tac THEN Cases_on `beh` THEN
  simp [semanticsTheory.semantics_prog_def, semanticsTheory.evaluate_prog_with_clock_def,
        evaluateTheory.evaluate_decs_def]);
val _ = (print "empty_iff="; print_thm empty_iff; print "\n");
val result = rhs (concl (EVAL ``SND (semantics$evaluate_prog_with_clock
  (ARB:num semanticPrimitives$state) <| v := Bind [] []; c := Bind [] [] |> 8 [])``));
val _ = (print "empty_result="; print_term result; print "\n");
