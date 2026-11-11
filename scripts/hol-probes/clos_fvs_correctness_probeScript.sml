(* Typed source statements for closure free-variable removal. *)
load "clos_fvsProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_typed=" clos_fvsTheory.remove_fvs_def;
val _ = show "remove_sing_typed=" clos_fvsTheory.remove_fvs_sing_def;
val _ = show "remove_sing_eq_typed=" clos_fvsTheory.remove_fvs_sing_eq;
val _ = show "remove_length_typed=" clos_fvsTheory.LENGTH_remove_fvs;
val _ = show "compile_typed=" clos_fvsTheory.compile_def;
val _ = show "compile_eq_typed=" clos_fvsTheory.compile_eq;
val _ = show "compile_inc_typed=" clos_fvsTheory.compile_inc_def;
val _ = show "code_rel_typed=" clos_fvsProofTheory.code_rel_def;
val _ = show "function_rel_typed=" clos_fvsProofTheory.f_rel_def;
val _ = show "value_rel_typed=" clos_fvsProofTheory.v_rel_rules;
val _ = show "ref_rel_typed=" clos_fvsProofTheory.ref_rel_rules;
val _ = show "state_rel_typed=" clos_fvsProofTheory.state_rel_def;
val state_rel_dec_clock_replay = Q.prove (
  `clos_fvsProof$state_rel (s1 :('c,'ffi) closSem$state) s2 ==>
   clos_fvsProof$state_rel (closSem$dec_clock 1 s1) (closSem$dec_clock 1 s2)`,
  simp [clos_fvsProofTheory.state_rel_def, closSemTheory.dec_clock_def]);
val _ = show "state_rel_dec_clock_typed=" state_rel_dec_clock_replay;
val do_app_statement = ``clos_fvsProof$state_rel (s :('c,'ffi) closSem$state) t /\
  LIST_REL clos_fvsProof$v_rel xs ys ==>
  case closSem$do_app opp xs s of
    | Rerr err1 => ?err2. closSem$do_app opp ys t = Rerr err2 /\
                           exc_rel clos_fvsProof$v_rel err1 err2
    | Rval (x, s1) => ?y t1. clos_fvsProof$v_rel x y /\
         clos_fvsProof$state_rel s1 t1 /\ closSem$do_app opp ys t = Rval (y, t1)``;
val _ = (print "do_app_statement_typed="; print_term do_app_statement; print "\n");
val bytes_statement = ``clos_fvsProof$v_rel x y ==> closSem$v_to_bytes y = closSem$v_to_bytes x``;
val words_statement = ``clos_fvsProof$v_rel x y ==> closSem$v_to_words y = closSem$v_to_words x``;
val install_statement = ``clos_fvsProof$state_rel (s :('c,'ffi) closSem$state) t /\
  LIST_REL clos_fvsProof$v_rel xs ys ==>
  case closSem$do_install xs s of
    | (Rerr err1, s1) => ?err2 t1. closSem$do_install ys t = (Rerr err2, t1) /\
         exc_rel clos_fvsProof$v_rel err1 err2 /\ clos_fvsProof$state_rel s1 t1
    | (Rval exps1, s1) => ?exps2 t1. clos_fvsProof$state_rel s1 t1 /\ exps1 <> [] /\
         clos_fvsProof$code_rel 0 exps1 exps2 /\ closSem$do_install ys t = (Rval exps2, t1)``;
val _ = (print "bytes_statement_typed="; print_term bytes_statement; print "\n");
val _ = (print "words_statement_typed="; print_term words_statement; print "\n");
val _ = (print "install_statement_typed="; print_term install_statement; print "\n");
val update_thunk_statement = ``clos_fvsProof$state_rel (s1 :('c,'ffi) closSem$state) s2 /\
  LIST_REL clos_fvsProof$v_rel vs ys ==>
    (closSem$update_thunk [closSem$RefPtr v ptr] s1.refs vs = NONE ==>
       closSem$update_thunk [closSem$RefPtr v ptr] s2.refs ys = NONE) /\
    (closSem$update_thunk [closSem$RefPtr v ptr] s1.refs vs = SOME refs1 ==>
       ?refs2. closSem$update_thunk [closSem$RefPtr v ptr] s2.refs ys = SOME refs2 /\
               clos_fvsProof$state_rel (s1 with refs := refs1) (s2 with refs := refs2))``;
val _ = (print "update_thunk_statement_typed="; print_term update_thunk_statement; print "\n");
val _ = show "dest_closure_some_typed=" clos_fvsProofTheory.dest_closure_SOME_IMP;
val _ = show "dest_closure_full_typed=" clos_fvsProofTheory.dest_closure_SOME_Full_app;
val _ = show "evaluate_remove_typed=" clos_fvsProofTheory.evaluate_remove_fvs;
val _ = show "remove_correct_typed=" clos_fvsProofTheory.remove_fvs_correct;
val _ = show "semantics_compile_typed=" clos_fvsProofTheory.semantics_compile;
val _ = show "remove_vars_none_typed=" clos_fvsProofTheory.remove_fvs_every_Fn_vs_NONE;
val _ = show "remove_obeys_max_app_typed=" clos_fvsProofTheory.remove_fvs_obeys_max_app;
val _ = show "remove_fv_max_typed=" clos_fvsProofTheory.fv_max_remove_fvs;
val _ = show "remove_set_globals_typed=" clos_fvsProofTheory.remove_fvs_set_globals;
val _ = show "remove_elist_globals_typed=" clos_fvsProofTheory.remove_fvs_elist_globals;
val _ = show "remove_esgc_free_typed=" clos_fvsProofTheory.remove_fvs_esgc_free;
