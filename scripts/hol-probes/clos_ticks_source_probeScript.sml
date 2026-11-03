(* Typed source declarations for closure tick removal. *)
load "clos_ticksProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_sing_typed" clos_ticksTheory.remove_ticks_sing_def;
val _ = show "remove_sing_eq_typed" clos_ticksTheory.remove_ticks_sing_eq;
val _ = show "compile_inc_typed" clos_ticksTheory.compile_inc_def;
val _ = show "code_rel_typed" clos_ticksProofTheory.code_rel_def;
val _ = show "function_rel_typed" clos_ticksProofTheory.f_rel_def;
val _ = show "value_rel_typed" clos_ticksProofTheory.v_rel_rules;
val _ = show "ref_rel_typed" clos_ticksProofTheory.ref_rel_rules;
val _ = show "state_rel_typed" clos_ticksProofTheory.state_rel_def;
val _ = show "code_rel_length_typed" clos_ticksProofTheory.code_rel_IMP_LENGTH;
val _ = show "state_rel_max_app_typed" clos_ticksProofTheory.state_rel_IMP_max_app_EQ;
val _ = show "state_rel_clock_typed" clos_ticksProofTheory.state_rel_clock;
val _ = show "mk_ticks_typed" clos_ticksProofTheory.mk_Ticks_def;
val _ = show "remove_mk_ticks_typed" clos_ticksProofTheory.remove_ticks_mk_Ticks;
val _ = show "evaluate_mk_ticks_typed" clos_ticksProofTheory.evaluate_mk_Ticks;
val _ = show "evaluate_remove_ticks_typed" clos_ticksProofTheory.evaluate_remove_ticks;
val _ = show "remove_var_ticks_typed" clos_ticksProofTheory.remove_ticks_Var_IMP_mk_Ticks;
val _ = show "remove_raise_ticks_typed" clos_ticksProofTheory.remove_ticks_Raise_IMP_mk_Ticks;
val _ = show "remove_handle_ticks_typed" clos_ticksProofTheory.remove_ticks_Handle_IMP_mk_Ticks;
val _ = show "remove_let_ticks_typed" clos_ticksProofTheory.remove_ticks_Let_IMP_mk_Ticks;
val _ = show "remove_if_ticks_typed" clos_ticksProofTheory.remove_ticks_If_IMP_mk_Ticks;
val _ = show "remove_fn_ticks_typed" clos_ticksProofTheory.remove_ticks_Fn_IMP_mk_Ticks;
val _ = show "remove_letrec_ticks_typed" clos_ticksProofTheory.remove_ticks_Letrec_IMP_mk_Ticks;
val state_rel_dec_clock_replay = Q.prove (
  `clos_ticksProof$state_rel (s1 :('c,'ffi) closSem$state) s2 ==>
   clos_ticksProof$state_rel (closSem$dec_clock 1 s1) (closSem$dec_clock 1 s2)`,
  simp [clos_ticksProofTheory.state_rel_def, closSemTheory.dec_clock_def]);
val _ = show "state_rel_dec_clock_typed" state_rel_dec_clock_replay;
