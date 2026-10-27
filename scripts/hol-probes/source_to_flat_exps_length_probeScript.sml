load "source_to_flatTheory";
open HolKernel Parse boolLib bossLib source_to_flatTheory;
val _ = Globals.linewidth := 1000000;

(* Replay the local theorem from source_to_flatProofScript.sml over the
   original compiler definition; the proof theory need not be loaded. *)
val length_thm = prove(
  ``LENGTH (compile_exps t m es) = LENGTH es``,
  Induct_on `es` >> rw [compile_exp_def]);
val _ = if null (hyp length_thm) then () else raise Fail "unexpected assumptions";
val _ = (print "compile_exps_length="; print_term (concl length_thm); print "\n");
val _ = (print "compile_exps_length_typed=";
         Lib.with_flag (Globals.show_types,true) print_term (concl length_thm); print "\n");
