(* Typed captures for three backendProof pipeline-shape rules (task 273): the
   attachment result, the lab configuration exposed on success, and the lab
   program behind a successful stack pipeline. *)
load "preamble";
load "backendProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble backendProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "backendProof", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in backendProof>\n");

val _ = emit "attach_bitmaps_SOME_typed" "attach_bitmaps_SOME";
val _ = emit "from_lab_conf_EX_typed" "from_lab_conf_EX";
val _ = emit "from_stack_conf_EX_typed" "from_stack_conf_EX";
