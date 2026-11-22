(* Typed captures for the data_to_word_assignProof Install/CopyByte group
   (assign_Install, assign_CopyByte and their prerequisites), kept separate from
   data_to_word_assign_typed_probe so that the two porting branches do not edit
   the same probe. All captured theorems are exported and fetched from the
   theory DB. *)
load "preamble";
load "data_to_word_assignProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun cap label name = emit label (DB.fetch "data_to_word_assignProof" name);

val _ = cap "evaluate_BignumHalt_typed" "evaluate_BignumHalt";
val _ = cap "do_app_safe_for_space_allowed_op_typed" "do_app_safe_for_space_allowed_op";
val _ = cap "InstallCode_code_thm_typed" "InstallCode_code_thm";
val _ = cap "InstallData_code_thm_typed" "InstallData_code_thm";
val _ = cap "assign_Install_typed" "assign_Install";
val _ = cap "CopyByteAdd_thm_typed" "CopyByteAdd_thm";
val _ = cap "CopyByteSub_thm_typed" "CopyByteSub_thm";
val _ = cap "assign_CopyByte_typed" "assign_CopyByte";
