load "flat_to_closProofTheory";
open HolKernel Parse boolLib bossLib;
open flat_to_closProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "findi_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl indexedListsTheory.findi_def); print "\n");
val _ = (print "compile_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_def); print "\n");
val _ = (print "compile_decs_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_decs_def); print "\n");
val _ = (print "compile_op_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_op_def); print "\n");
val _ = (print "compile_arith_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.compile_arith_def); print "\n");
val _ = (print "copy_str_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.CopyByteStr_def); print "\n");
val _ = (print "copy_aw8_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flat_to_closTheory.CopyByteAw8_def); print "\n");
val _ = (print "rules_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_rules); print "\n");
val _ = (print "induction_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_ind); print "\n");
val _ = (print "cases_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl v_rel_cases); print "\n");
(* Typed replay of state_rel_dec_clock[local], which is not exported. *)
val state_clock_replay = prove
  (``!(s : ('a, 'b) flatSem$state) (t : ('a, 'b) closSem$state).
      state_rel s t ==> s.clock = t.clock /\
        state_rel (flatSem$dec_clock s) (closSem$dec_clock 1 t)``,
   simp [state_rel_def, flatSemTheory.dec_clock_def, closSemTheory.dec_clock_def]);
val _ = (print "state_rel_dec_clock_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl state_clock_replay); print "\n");
val _ = (print "state_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl state_rel_def); print "\n");
val _ = (print "lookup_refv_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_refv); print "\n");
val _ = (print "lookup_byte_array_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_byte_array); print "\n");
val _ = (print "lookup_array_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_array); print "\n");
val _ = (print "lookup_thunk_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl lookup_thunk); print "\n");
val _ = (print "store_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl store_rel_def); print "\n");
val _ = (print "inc_compile_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl inc_compile_decs'_def); print "\n");
val _ = (print "install_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl install_config_rel'_def); print "\n");
val _ = (print "exc_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.exc_rel_def); print "\n");
val _ = (print "result_rel_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl semanticPrimitivesPropsTheory.result_rel_def); print "\n");
val _ = (print "clos_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl closSemTheory.semantics_def); print "\n");
val _ = (print "compile_semantics_prime_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_semantics'); print "\n");
val _ = (print "install_rel_unprimed_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl install_config_rel_def); print "\n");
val _ = (print "compile_semantics_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_semantics); print "\n");
val _ = (print "compile_correct_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl compile_correct); print "\n");
