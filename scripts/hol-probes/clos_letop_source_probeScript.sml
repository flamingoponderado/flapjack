(* Typed source declarations for closure let-operation cleanup. *)
load "preamble";
load "clos_letopProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble closSemTheory clos_letopTheory clos_letopProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "var_list_typed" clos_letopTheory.var_list_def;
val _ = show "dest_op_typed" clos_letopTheory.dest_op_def;
val _ = show "let_op_sing_typed" clos_letopTheory.let_op_sing_def;
val _ = show "let_op_sing_eq_typed" clos_letopTheory.let_op_sing_eq;
val _ = show "compile_inc_typed" clos_letopTheory.compile_inc_def;
val _ = show "var_list_length_typed" clos_letopProofTheory.var_list_IMP_LENGTH;
val var_list_evaluate_replay = prove(
  ``!a2 a1 xs (ys:closLang$exp list) (s:('c,'ffi) closSem$state) env.
      var_list (LENGTH a1) xs ys /\ LENGTH ys = LENGTH a2 ==>
      evaluate (xs,a1++a2++env,s) = (Rval a2,s)``,
  Induct THEN1 (rw [] \\ imp_res_tac var_list_IMP_LENGTH \\ fs [])
  \\ Cases_on `ys` \\ fs [LENGTH]
  \\ Cases_on `xs` \\ fs [var_list_def]
  \\ Cases_on `h'` \\ fs [var_list_def]
  \\ once_rewrite_tac [closPropsTheory.evaluate_CONS]
  \\ fs [evaluate_def, EL_LENGTH_APPEND] \\ rw []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ first_x_assum (qspec_then `a1 ++ [h']` mp_tac)
  \\ fs [] \\ rw [] \\ res_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]);
val _ = show "var_list_evaluate_replay_typed" var_list_evaluate_replay;
val var_list_evaluate_zero_replay = prove(
  ``!vs xs (ys:closLang$exp list) (s:('c,'ffi) closSem$state) env.
      var_list 0 xs ys /\ LENGTH ys = LENGTH vs ==>
        evaluate (xs, vs ++ env, s) = (Rval vs, s)``,
  rw []
  \\ match_mp_tac (Q.SPECL [`vs`, `[]`] var_list_evaluate_replay
       |> SIMP_RULE std_ss [APPEND,LENGTH])
  \\ asm_exists_tac \\ fs []);
val _ = show "var_list_evaluate_zero_replay_typed" var_list_evaluate_zero_replay;
val _ = show "code_rel_typed" clos_letopProofTheory.code_rel_def;
val _ = show "code_rel_length_typed" clos_letopProofTheory.code_rel_IMP_LENGTH;
val _ = show "code_rel_cons_typed" clos_letopProofTheory.code_rel_CONS_CONS;
val _ = show "function_rel_typed" clos_letopProofTheory.f_rel_def;
val _ = show "value_rel_typed" clos_letopProofTheory.v_rel_rules;
val _ = show "ref_rel_typed" clos_letopProofTheory.ref_rel_rules;
val _ = show "fmap_rel_typed" clos_letopProofTheory.FMAP_REL_def;
val _ = show "state_rel_typed" clos_letopProofTheory.state_rel_def;
val _ = show "evaluate_let_op_typed" clos_letopProofTheory.evaluate_let_op;
val state_rel_dec_clock_replay = prove(
  ``state_rel s1 s2 ==> state_rel (dec_clock 1 s1) (dec_clock 1 s2)``,
  rw [state_rel_def, dec_clock_def, state_component_equality]);
val _ = show "state_rel_dec_clock_replay_typed" state_rel_dec_clock_replay;
val simple_state_rel_replay = prove(
  ``closProps$simple_state_rel clos_letopProof$v_rel clos_letopProof$state_rel``,
  fs [closPropsTheory.simple_state_rel_def, state_rel_def]
  \\ rw [] \\ fs [FMAP_REL_def, FLOOKUP_DEF]
  \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);
val _ = show "simple_state_rel_replay_typed" simple_state_rel_replay;
val do_app_lemma_replay = prove(
  ``state_rel s t /\ LIST_REL v_rel xs ys ==>
    case do_app opp xs s of
      | Rerr err1 => ?err2. do_app opp ys t = Rerr err2 /\ exc_rel v_rel err1 err2
      | Rval (x, s1) => ?y t1. v_rel x y /\ state_rel s1 t1 /\
                               do_app opp ys t = Rval (y, t1)``,
  match_mp_tac closPropsTheory.simple_val_rel_do_app
  \\ fs [closPropsTheory.simple_val_rel_def, simple_state_rel_replay] \\ rw [] \\ fs [v_rel_cases]);
val _ = show "do_app_lemma_replay_typed" do_app_lemma_replay;
