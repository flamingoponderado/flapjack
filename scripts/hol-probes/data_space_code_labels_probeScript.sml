load "data_spaceProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "get_code_labels_compile="; print_thm data_spaceProofTheory.get_code_labels_compile; print "\n");
val _ = (print "compile_type="; print (type_to_string (type_of ``data_space$compile``)); print "\n");
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "get_code_labels_space_typed="; print_term (concl data_spaceProofTheory.get_code_labels_space); print "\n");
val _ = (print "get_vars_IMP_LENGTH_typed="; print_term (concl data_spaceProofTheory.get_vars_IMP_LENGTH); print "\n");
val _ = (print "do_stack_with_space_typed="; print_term (concl data_spaceProofTheory.do_stack_with_space); print "\n");
val _ = (print "do_stack_with_locals_typed="; print_term (concl data_spaceProofTheory.do_stack_with_locals); print "\n");
val _ = (print "locals_ok_def_typed="; print_term (concl dataPropsTheory.locals_ok_def); print "\n");
val _ = (print "locals_ok_get_vars_typed="; print_term (concl dataPropsTheory.locals_ok_get_vars); print "\n");
val _ = (print "locals_ok_cut_env_typed="; print_term (concl dataPropsTheory.locals_ok_cut_env); print "\n");
val _ = (print "locals_ok_refl_typed="; print_term (concl dataPropsTheory.locals_ok_refl); print "\n");
val _ = (print "evaluate_locals_typed="; print_term (concl dataPropsTheory.evaluate_locals); print "\n");
(* The original evaluate_compile is local; print its literal source statement with inferred types. *)
val _ = (print "evaluate_compile_statement_typed="; print_term
  ``!c s res s2 vars l.
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      (dataSem$evaluate (c,s) = (res,s2)) /\
      dataProps$locals_ok s.locals l ==>
      ?w safe peak smx.
        (dataSem$evaluate (data_space$compile c, s with locals := l) =
           (res,if res = NONE then s2 with <| locals := w; safe_for_space := safe;
             peak_heap_length := peak; stack_max := smx |>
            else s2 with <| safe_for_space := safe; peak_heap_length := peak; stack_max := smx |>)) /\
        dataProps$locals_ok s2.locals w``; print "\n");
val _ = (print "compile_correct_typed="; print_term (concl data_spaceProofTheory.compile_correct); print "\n");
