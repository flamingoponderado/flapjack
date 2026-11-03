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
val _ = show "remove_call_ticks_typed" clos_ticksProofTheory.remove_ticks_Call_IMP_mk_Ticks;
val _ = show "remove_tick_typed" clos_ticksProofTheory.remove_ticks_Tick;
val _ = show "remove_app_ticks_typed" clos_ticksProofTheory.remove_ticks_App_IMP_mk_Ticks;
val _ = show "dest_closure_shape_typed" clos_ticksProofTheory.dest_closure_SOME_IMP;
val _ = show "remove_op_ticks_typed" clos_ticksProofTheory.remove_ticks_Op_IMP_mk_Ticks;
val _ = show "simple_val_rel_typed" clos_ticksProofTheory.simple_val_rel;
val _ = show "simple_state_rel_typed" clos_ticksProofTheory.simple_state_rel;
val do_app_lemma_replay = Q.prove (
  `clos_ticksProof$state_rel (s :('c,'ffi) closSem$state) t /\
   LIST_REL clos_ticksProof$v_rel xs ys ==>
   case closSem$do_app opp ys t of
     | Rerr err2 => ?err1. closSem$do_app opp xs s = Rerr err1 /\
                            exc_rel clos_ticksProof$v_rel err1 err2
     | Rval (y,t1) => ?x s1. clos_ticksProof$v_rel x y /\
                              clos_ticksProof$state_rel s1 t1 /\
                              closSem$do_app opp xs s = Rval (x,s1)`,
  metis_tac [closPropsTheory.simple_val_rel_do_app_rev,
    clos_ticksProofTheory.simple_val_rel, clos_ticksProofTheory.simple_state_rel]);
val _ = show "do_app_lemma_typed" do_app_lemma_replay;
val bytes_statement = Q.prove (
  `clos_ticksProof$v_rel x y ==> closSem$v_to_bytes y = closSem$v_to_bytes x`,
  metis_tac [clos_ticksProofTheory.simple_val_rel, closPropsTheory.simple_val_rel_v_to_bytes]);
val words_statement = Q.prove (
  `clos_ticksProof$v_rel x y ==> closSem$v_to_words y = closSem$v_to_words x`,
  metis_tac [clos_ticksProofTheory.simple_val_rel, closPropsTheory.simple_val_rel_v_to_words]);
val _ = show "bytes_statement_typed" bytes_statement;
val _ = show "words_statement_typed" words_statement;
val do_install_lemma_replay = Q.prove (
  `clos_ticksProof$state_rel (s :('c,'ffi) closSem$state) t /\
   LIST_REL clos_ticksProof$v_rel xs ys ==>
   case closSem$do_install xs s of
     | (Rerr err1,s1) => ?err2 t1. closSem$do_install ys t = (Rerr err2,t1) /\
                            exc_rel clos_ticksProof$v_rel err1 err2 /\ clos_ticksProof$state_rel s1 t1
     | (Rval exps1,s1) => ?exps2 t1. clos_ticksProof$state_rel s1 t1 /\ exps1 <> [] /\
                            clos_ticksProof$code_rel exps1 exps2 /\
                            closSem$do_install ys t = (Rval exps2,t1)`,
  ho_match_mp_tac (Q.SPEC `clos_ticks$compile_inc` closPropsTheory.simple_val_rel_do_install) >>
  simp [clos_ticksProofTheory.simple_val_rel, clos_ticksProofTheory.simple_state_rel,
    closPropsTheory.simple_compile_state_rel_def, clos_ticksTheory.compile_inc_def,
    clos_ticksProofTheory.code_rel_def, clos_ticksProofTheory.state_rel_def,
    pairTheory.FORALL_PROD, miscTheory.shift_seq_def, backendPropsTheory.pure_co_def, FUN_EQ_THM] >>
  metis_tac [clos_ticksProofTheory.remove_ticks_IMP_LENGTH]);
val _ = show "do_install_lemma_typed" do_install_lemma_replay;
val state_rel_dec_clock_replay = Q.prove (
  `clos_ticksProof$state_rel (s1 :('c,'ffi) closSem$state) s2 ==>
   clos_ticksProof$state_rel (closSem$dec_clock 1 s1) (closSem$dec_clock 1 s2)`,
  simp [clos_ticksProofTheory.state_rel_def, closSemTheory.dec_clock_def]);
val _ = show "state_rel_dec_clock_typed" state_rel_dec_clock_replay;
