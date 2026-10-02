(* Original full LocValue case2099-2106, restated standalone. Original
   last_x_assum/reverse CASE_TAC depend on induction-context assumption order;
   standalone replay uses the same evaluate/comp/reg_bound equations and
   code_rel_loc_check/state_rel_set_var facts, with no new premise. *)
load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble wordsTheory stack_removeProofTheory stack_removeTheory stackSemTheory stackPropsTheory stackLangTheory set_sepTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val _ = Globals.linewidth := 20000;
val cl = prove(``!s1 r s2 t1 k off jump dst l1 l2.
  stackSem$evaluate ((stackLang$LocValue dst l1 l2 : 'a stackLang$prog),(s1:('a,'b,'c)stackSem$state)) = (r,s2) /\ r <> SOME stackSem$Error /\
  state_rel jump off k s1 t1 /\ reg_bound (stackLang$LocValue dst l1 l2 : 'a stackLang$prog) k ==>
  ?ck t2. stackSem$evaluate (comp jump off k (stackLang$LocValue dst l1 l2 : 'a stackLang$prog),t1 with clock := ck + t1.clock) = (r,t2) /\
    (case r of SOME(stackSem$Halt _) => t2.ffi = s2.ffi
     | SOME stackSem$TimeOut => t2.ffi = s2.ffi
     | SOME(stackSem$FinalFFI _) => t2.ffi = s2.ffi
     | _ => state_rel jump off k s2 t2)``,
  rpt gen_tac >> strip_tac >> qexists_tac `0` >>
  fs [Once comp_def, evaluate_def, reg_bound_def] >>
  every_case_tac >> fs [] >> rw [] >>
  imp_res_tac code_rel_loc_check >>
  fs [state_rel_def] >>
  metis_tac [state_rel_set_var, code_rel_loc_check]);
val _ = print("cl_statement=" ^ term_to_string(concl cl) ^ "\n");
val _ = print("cl_proved=" ^ term_to_string(rhs(concl(EQT_INTRO cl))) ^ "\n");
