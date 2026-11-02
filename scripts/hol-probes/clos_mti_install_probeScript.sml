load "preamble"; load "clos_mtiProofTheory";
open HolKernel Parse bossLib preamble backendPropsTheory closPropsTheory
     clos_mtiTheory closSemTheory clos_mtiProofTheory;
val _ = new_theory "flapjack_clos_mti_install_replay";
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
fun bring_fwd_ctors th ty = map ((fn s => Parse.bring_to_front_overload s {Name = s, Thy = th}) o term_to_string) (TypeBase.constructors_of ty);
val _ = bring_fwd_ctors "closLang" ``:closLang$exp``;

(* Replay the local lookup lemma used by the thunk-update case. *)
Theorem state_rel_opt_rel_refs_replay:
  (state_rel s1 s2 ∧ FLOOKUP s1.refs n = r1 ⇒
     ∃r2. FLOOKUP s2.refs n = r2 ∧ OPTREL (ref_rel s1.max_app) r1 r2) ∧
  (state_rel s1 s2 ∧ FLOOKUP s2.refs n = r2 ⇒
     ∃r1. FLOOKUP s1.refs n = r1 ∧ OPTREL (ref_rel s1.max_app) r1 r2)
Proof
  rw [] \\ gvs [state_rel_def, FMAP_REL_def, FLOOKUP_DEF] \\ rw []
QED

Theorem rel_update_thunk_replay:
  state_rel s1 s2 ∧
  LIST_REL (v_rel s1.max_app) vs ys ⇒
    (update_thunk [RefPtr v ptr] s2.refs ys = NONE ⇒
       update_thunk [RefPtr v ptr] s1.refs vs = NONE) ∧
    (update_thunk [RefPtr v ptr] s2.refs ys = SOME refs2 ⇒
       ∃refs1. update_thunk [RefPtr v ptr] s1.refs vs = SOME refs1 ∧
               state_rel (s1 with refs := refs1) (s2 with refs := refs2))
Proof
  rw []
  \\ gvs [oneline update_thunk_def, AllCaseEqs()] \\ rw []
  \\ gvs [oneline dest_thunk_def, AllCaseEqs()]
  \\ (
    gvs [Once v_rel_cases, oneline store_thunk_def, AllCaseEqs()]
    \\ TRY (
      drule_all (cj 2 state_rel_opt_rel_refs_replay) \\ rw [OPTREL_def]
      \\ rgs [Once ref_rel_cases])
    \\ TRY (
      drule (cj 1 state_rel_opt_rel_refs_replay) \\ strip_tac
      \\ first_x_assum dxrule \\ rw [OPTREL_def] \\ gvs []
      \\ imp_res_tac (cj 2 state_rel_opt_rel_refs_replay) \\ gvs [OPTREL_def]
      \\ rgs [Once ref_rel_cases])
    \\ gvs [state_rel_def, FMAP_REL_def, FLOOKUP_UPDATE] \\ rw []
    \\ simp [ref_rel_def]
    \\ metis_tac [])
QED

(* Replay the source's local do_install_lemma with the original proof. *)
val do_install_inst =
  simple_val_rel_do_install
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`,
        `cr`|->`code_rel s.max_app`]
  |> SIMP_RULE bool_ss [simple_val_rel, simple_state_rel]
  |> Q.SPEC `clos_mti$compile_inc s.max_app`;

Theorem do_install_replay:
    state_rel s t /\ LIST_REL (v_rel s.max_app) xs ys ==>
    case do_install xs s of
      | (Rerr err1, s1) => ?err2 t1. do_install ys t = (Rerr err2, t1) /\
                            exc_rel (v_rel s.max_app) err1 err2 /\
                            s1.max_app = s.max_app /\ state_rel s1 t1
      | (Rval exps1, s1) => ?exps2 t1. (s1.max_app = s.max_app /\
                               state_rel s1 t1) /\ (~ (exps1 = [])) /\
                               code_rel s.max_app exps1 exps2 /\
                               do_install ys t = (Rval exps2, t1)
Proof
  strip_tac
  \\ irule do_install_inst
  \\ fs [simple_compile_state_rel_def, simple_state_rel]
  \\ qexists_tac `s`
  \\ fs [compile_inc_def, pairTheory.FORALL_PROD,
            clos_mtiTheory.intro_multi_length, code_rel_def, state_rel_def]
  \\ rw [shift_seq_def, backendPropsTheory.pure_co_def, FUN_EQ_THM] \\ rfs []
  \\ fs [PAIR_FST_SND_EQ] \\ rveq \\ fs []
QED

fun show_thm label th =
  if null (hyp th) then
    (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "do_install_replay_typed=" do_install_replay;
val _ = show_thm "state_rel_opt_rel_refs_replay_typed=" state_rel_opt_rel_refs_replay;
val _ = show_thm "rel_update_thunk_replay_typed=" rel_update_thunk_replay;
