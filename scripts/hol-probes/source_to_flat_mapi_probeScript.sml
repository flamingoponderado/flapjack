load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "mapi_map_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl source_to_flatProofTheory.mapi_map); print "\n");
val _ = (print "filter_mapi_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl source_to_flatProofTheory.FILTER_MAPi_ID); print "\n");

(* Replay the original local tuple projection theorem with inferred types. *)
val fst_lem_replay = prove (
  ``(λ(p1,p1',p2). p1) = FST``,
  rw [FUN_EQ_THM] >> pairarg_tac >> rw []);
val _ = if null (hyp fst_lem_replay) then () else raise Fail "unexpected hypotheses";
val _ = (print "fst_lem_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl fst_lem_replay); print "\n");
