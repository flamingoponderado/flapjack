(* Typed source declarations for the wordConvs predicate laws (task 240).
   All four targets are exported theorems of wordConvsTheory, so they are
   fetched from the theory database. *)
load "preamble";
load "wordConvsTheory";
open HolKernel Parse boolLib bossLib;
open preamble wordConvsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="wordConvs",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by wordConvs")
  | SOME (th,_) => show label th;

val _ = emit "wc_every_var_inst_conj_typed" "every_var_inst_conj";
val _ = emit "wc_every_var_exp_conj_typed" "every_var_exp_conj";
val _ = emit "wc_every_var_conj_typed" "every_var_conj";
val _ = emit "wc_not_created_subprogs_P_typed" "not_created_subprogs_P_def";
