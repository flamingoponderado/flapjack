load "preamble"; load "word_cseProofTheory";
open HolKernel Parse bossLib preamble word_cseProofTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val _ = (print "ie_full="; print_thm insert_eq; print "\n");
val replay = prove(concl insert_eq, rpt strip_tac \\ eq_tac \\ gvs [] \\ strip_tac
  \\ ‘lookup n1 (insert n1 v1 l) = lookup n1 (insert n1 v2 l)’ by asm_rewrite_tac []
  \\ gvs []);
val _ = (if null(hyp replay) then () else raise Fail "open premise"; print "ie_replay="; print_thm replay; print "\n");
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "ie_0_7" ``insert 0 7 (LN:num num_map) = insert 0 7 (LN)``;
val _ = out "ie_0_8" ``insert 0 7 (LN:num num_map) = insert 0 8 (LN)``;
val _ = out "ie_1_7" ``insert 7 7 (LS 99:num num_map) = insert 7 7 (LS 99)``;
val _ = out "ie_1_8" ``insert 7 7 (LS 99:num num_map) = insert 7 8 (LS 99)``;
val _ = out "ie_2_7" ``insert 0 7 (BN LN LN:num num_map) = insert 0 7 (BN LN LN)``;
val _ = out "ie_2_8" ``insert 0 7 (BN LN LN:num num_map) = insert 0 8 (BN LN LN)``;
val _ = out "ie_3_7" ``insert 2 7 (BS LN 11 LN:num num_map) = insert 2 7 (BS LN 11 LN)``;
val _ = out "ie_3_8" ``insert 2 7 (BS LN 11 LN:num num_map) = insert 2 8 (BS LN 11 LN)``;
val _ = out "ie_4_7" ``insert 1 7 (BN (LS 8) (LS 9):num num_map) = insert 1 7 (BN (LS 8) (LS 9))``;
val _ = out "ie_4_8" ``insert 1 7 (BN (LS 8) (LS 9):num num_map) = insert 1 8 (BN (LS 8) (LS 9))``;

val _ = (print "ie_binder_types="; List.app (fn v => (print_term v; print ":"; print_type(type_of v); print " ")) (#1(strip_forall(concl insert_eq))); print "\n");
(* Binder types are the final captured row. *)
