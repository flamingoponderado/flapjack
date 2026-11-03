(* Typed source statements for closure free-variable removal. *)
load "clos_fvsProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_sing_typed=" clos_fvsTheory.remove_fvs_sing_def;
val _ = show "remove_sing_eq_typed=" clos_fvsTheory.remove_fvs_sing_eq;
val _ = show "remove_length_typed=" clos_fvsTheory.LENGTH_remove_fvs;
val _ = show "compile_typed=" clos_fvsTheory.compile_def;
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
val _ = show "evaluate_remove_typed=" clos_fvsProofTheory.evaluate_remove_fvs;
val _ = show "semantics_compile_typed=" clos_fvsProofTheory.semantics_compile;
