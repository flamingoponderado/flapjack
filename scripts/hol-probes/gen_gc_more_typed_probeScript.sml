(* Typed captures for remaining gen_gcScript heap declarations (task 273): the
   lookup extension and boundary rules, membership of a successful lookup, the
   pointer reachability step, and the forwarding-pointer status rule. *)
load "preamble";
load "gen_gcTheory";
open HolKernel Parse boolLib bossLib;
open preamble gen_gcTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "gen_gc", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in gen_gc>\n");

val _ = emit "heap_lookup_EXTEND_typed" "heap_lookup_EXTEND";
val _ = emit "LESS_IMP_heap_lookup_typed" "LESS_IMP_heap_lookup";
val _ = emit "heap_lookup_IMP_MEM_typed" "heap_lookup_IMP_MEM";
val _ = emit "heap_lookup_LENGTH_typed" "heap_lookup_LENGTH";
val _ = emit "IMP_reachable_addresses_typed" "IMP_reachable_addresses";
val _ = emit "gc_forward_ptr_ok_typed" "gc_forward_ptr_ok";
