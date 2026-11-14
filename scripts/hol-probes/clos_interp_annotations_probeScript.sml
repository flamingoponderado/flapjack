load "preamble"; load "clos_interpProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble closLangTheory closPropsTheory clos_interpTheory;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "every_Fn_vs_NONE_insert_interp_typed=" clos_interpProofTheory.every_Fn_vs_NONE_insert_interp;
val _ = show_thm "contains_App_SOME_insert_interp_typed=" clos_interpProofTheory.contains_App_SOME_insert_interp;
val opt_interp_lemma_replay = Q.prove (
  `opt_interp x = SOME x' ⇒
   set_globals x' = {||} ∧ set_globals x = {||} ∧
   (1 ≤ max_app ⇒ ¬contains_App_SOME max_app [x']) ∧
   every_Fn_vs_NONE [x'] ∧ no_mti x' ∧ esgc_free x ∧ esgc_free x'`,
  strip_tac \\ gvs [opt_interp_def,AllCaseEqs()] \\
  fs [no_mti_def,contains_App_SOME_def,op_gbag_def] \\
  qsuff_tac `
    (∀x. can_interpret x ⇒ set_globals x = {||} ∧ esgc_free x) ∧
    (∀x. can_interpret_list x ⇒ elist_globals x = {||} ∧ EVERY esgc_free x)`
  >- (rw [] \\ res_tac \\ fs []) \\
  rpt $ pop_assum kall_tac \\
  Induct \\ fs [can_interpret_def] \\
  Cases \\ fs [can_interpret_op_def,op_gbag_def] \\
  Cases_on `g` \\ fs [can_interpret_op_def,op_gbag_def]);
val _ = show_thm "opt_interp_lemma_replay_typed=" opt_interp_lemma_replay;
