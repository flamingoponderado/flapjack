load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib source_to_flatTheory source_to_flatProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp bind_locals_def) then () else raise Fail "unexpected definition hypotheses";
val _ = (print "bind_locals_def_typed=";
         Lib.with_flag (Globals.show_types,true) print_term (concl bind_locals_def); print "\n");

(* Replay the local theorem exactly as in source_to_flatProofScript.sml. *)
val append_thm = prove(
  ``∀funs.
    nsAppend (alist_to_ns (MAP (λx. (x,Local t x)) (MAP FST funs))) (bind_locals ts locals comp_map) =
    bind_locals (REPLICATE (LENGTH funs) t ++ ts) (MAP FST funs ++ locals) comp_map``,
  Induct_on `funs` >> fs [pairTheory.FORALL_PROD, bind_locals_def, namespaceTheory.nsBindList_def]);
val _ = if null (hyp append_thm) then () else raise Fail "unexpected theorem hypotheses";
val _ = (print "nsAppend_bind_locals_typed=";
         Lib.with_flag (Globals.show_types,true) print_term (concl append_thm); print "\n");
