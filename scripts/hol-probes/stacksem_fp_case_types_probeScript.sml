(* Full original carriers and all FP constructor payload types for the
complete StackSem FP branch review. No HOL-to-Lean equivalence claim. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun typ label t = (print(label ^ "="); print_type(type_of t); print "\n");
val _ = typ "fpc_inst" ``stackSem$inst``;
val _ = typ "fpc_constructor" ``asm$FP``;
val _ = typ "fpc_lookup" ``stackSem$get_fp_var``;
val _ = typ "fpc_update" ``stackSem$set_fp_var``;
val _ = typ "fpc_general_lookup" ``stackSem$get_var``;
val _ = typ "fpc_general_update" ``stackSem$set_var``;
val _ = (print "fpc_all_payloads=";
  app (fn c => (print (term_to_string c ^ ":" ^ type_to_string(type_of c) ^ ";")))
    (TypeBase.constructors_of ``:asm$fp``); print "\n");
