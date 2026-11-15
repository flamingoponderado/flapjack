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

(* Literal replays of clos_mtiProofScript.sml:163-173. *)
Theorem state_rel_max_app_replay:
  state_rel s t ⇒ s.max_app = t.max_app ∧ 1 ≤ t.max_app
Proof
  gvs [state_rel_def]
QED

Theorem state_rel_clocks_replay:
  state_rel s t ⇒ s.clock = t.clock
Proof
  gvs [state_rel_def]
QED

(* Literal replays of clos_mtiProofScript.sml:282-319 and 323-335. *)
Theorem mk_apps_err_1_replay:
    ∀ts other env1 s1 e3.
      evaluate (other,env1,s1) = (Rerr e2,s2) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e3 (ZIP (ts,other))],env1,s1) = (Rerr e2,s2)
Proof
  Induct
  \\ fs [evaluate_def]
  \\ Cases_on `other` \\ fs [ZIP,mk_Apps_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ fs [case_eq_thms,pair_case_eq]
  \\ rveq \\ fs [] \\ fs [evaluate_def]
QED

Theorem mk_apps_err_2_replay:
    ∀ts other env1 s1 e3 vs.
      evaluate ([e3],env1,s2) = (Rerr e2,s2') /\
      evaluate (other,env1,s1) = (Rval vs,s2) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e3 (ZIP (ts,other))],env1,s1) = (Rerr e2,s2')
Proof
  Induct
  \\ fs [evaluate_def,mk_Apps_def]
  \\ Cases_on `other` \\ fs [ZIP,mk_Apps_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ fs [case_eq_thms,pair_case_eq]
  \\ rveq \\ fs [] \\ fs [evaluate_def]
  \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
QED

Theorem evaluate_mk_apps_err_replay:
    !other ts env1 s1 vs.
      evaluate (other,env1,s1) = (Rval vs,s3) /\
      evaluate ([e],env1,s3) = (Rerr e3,s2') /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e (ZIP (ts,other))],env1,s1) = (Rerr e3,s2')
Proof
  Induct \\ Cases_on `ts` \\ fs [mk_Apps_def]
  \\ fs [evaluate_def]
  \\ simp [Once evaluate_CONS] \\ rw []
  \\ fs [case_eq_thms,pair_case_eq] \\ rveq
QED

(* Literal replay of clos_mtiProofScript.sml:344-367. *)
Theorem evaluate_mk_apps_ok_replay:
  !other ts env1 s1 vs.
      evaluate ([e],env1,s3) = (Rval [f],s2') /\
      evaluate (other,env1,s1) = (Rval vs,s3) /\
      LENGTH other = LENGTH ts ==>
      evaluate ([mk_Apps e (ZIP (ts,other))],env1,s1) =
      evaluate_apps f vs s2'
Proof
  once_rewrite_tac [CONJ_COMM]
  \\ Induct \\ Cases_on `ts` \\ fs [mk_Apps_def]
  \\ fs [evaluate_def,evaluate_apps_def]
  \\ simp [Once evaluate_CONS] \\ rw []
  \\ fs [case_eq_thms,pair_case_eq] \\ rveq
  \\ first_x_assum (qspec_then `t` mp_tac) \\ fs []
  \\ rpt (disch_then drule)
  \\ strip_tac \\ fs []
  \\ Cases_on `evaluate_apps f vs' s2'` \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs []
  \\ rveq \\ fs []
  \\ fs [evaluate_apps_def]
  \\ Cases_on `q` \\ fs []
  \\ imp_res_tac evaluate_SING \\ fs []
  \\ rveq \\ fs []
QED

(* Literal replays of clos_mtiProofScript.sml:379-394 and 455-484. *)
Theorem evaluate_apps_snoc_replay:
  !xs x f s.
    evaluate_apps f (SNOC x xs) s =
      case evaluate_app NONE f [x] s of
      | (Rval [v], s) => evaluate_apps v xs s
      | res => res
Proof
  Induct
  THEN1 (fs [evaluate_apps_def] \\ rw []
         \\ every_case_tac \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ fs [evaluate_apps_def] \\ rw []
  \\ Cases_on `evaluate_app NONE f [x] s` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []
QED

(* Literal replay of clos_mtiProofScript.sml:369-377. *)
Theorem dest_closure_none_apps_replay:
  !xs f1 s1.
      dest_closure s1.max_app NONE f1 [LAST xs] = NONE /\ xs <> [] ==>
      evaluate_apps f1 xs s1 = (Rerr (Rabort Rtype_error),s1)
Proof
  Induct \\ fs [evaluate_apps_def]
  \\ Cases_on `xs` \\ fs [evaluate_apps_def]
  \\ fs [evaluate_apps_def,evaluate_def]
QED

(* Literal replays of clos_mtiProofScript.sml:397-453. *)
Theorem evaluate_apps_timeout_replay:
  !ys ts s1 e1 env.
      s1.clock < LENGTH ys /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_snoc_replay]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock < LENGTH l` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]
QED

Theorem evaluate_apps_timeout_alt_replay:
  !ys ts s1 e1 env.
      s1.clock <= LENGTH ts /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1))
        ys s1 = (Rerr (Rabort Rtimeout_error),s1 with clock := 0)
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_snoc_replay]
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `(dec_clock 1 s1).clock <= LENGTH t` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [dec_clock_def]
QED

Theorem evaluate_apps_short_replay:
  !ys ts s1 e1 env.
      LENGTH ys <= s1.clock /\ LENGTH ys <= LENGTH ts /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
         (Rval [Closure NONE [] (ys ++ env) 1
                   (mk_Fns (DROP (LENGTH ys) ts) e1)],
          dec_clock (LENGTH ys) s1)
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_snoc_replay,evaluate_apps_def]
  THEN1 (fs [state_component_equality,dec_clock_def])
  \\ fs [evaluate_def,dest_closure_def,check_loc_def]
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `LENGTH l <= (dec_clock 1 s1).clock` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ disch_then drule
  \\ fs [dec_clock_def,ADD1]
QED

Theorem evaluate_apps_long_replay:
  !ys ts s1 e1 env.
      LENGTH ts < s1.clock /\ LENGTH ts < LENGTH ys /\
      1 ≤ s1.max_app ==>
      evaluate_apps (Closure NONE [] env 1 (mk_Fns ts e1)) ys s1 =
        case evaluate ([e1],REVERSE (TAKE (1+LENGTH ts) (REVERSE ys)) ++ env,
                dec_clock (1+LENGTH ts) s1) of
        | (Rval [v],s) =>
             evaluate_apps v (REVERSE (DROP (1+LENGTH ts) (REVERSE ys))) s
        | res => res
Proof
  recInduct SNOC_INDUCT \\ rw []
  \\ fs [evaluate_apps_snoc_replay,evaluate_apps_def]
  \\ fs [evaluate_def,Once dest_closure_def,check_loc_def]
  \\ Cases_on `ts` \\ fs [mk_Fns_def,evaluate_def]
  THEN1
   (fs [REVERSE_SNOC]
    \\ Cases_on `evaluate ([e1],x::env,dec_clock 1 s1)` \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `a` \\ fs []
    \\ Cases_on `t` \\ fs [])
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ `LENGTH t < (dec_clock 1 s1).clock` by (EVAL_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [EVAL ``(dec_clock 1 s).max_app``]
  \\ disch_then kall_tac
  \\ fs [REVERSE_SNOC] \\ fs [ADD1]
  \\ fs [dec_clock_def,ADD1]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

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
val _ = show_thm "state_rel_max_app_replay_typed=" state_rel_max_app_replay;
val _ = show_thm "state_rel_clocks_replay_typed=" state_rel_clocks_replay;
val _ = show_thm "evaluate_apps_snoc_replay_typed=" evaluate_apps_snoc_replay;
val _ = show_thm "evaluate_mk_apps_ok_replay_typed=" evaluate_mk_apps_ok_replay;
val _ = show_thm "mk_apps_err_1_replay_typed=" mk_apps_err_1_replay;
val _ = show_thm "mk_apps_err_2_replay_typed=" mk_apps_err_2_replay;
val _ = show_thm "evaluate_mk_apps_err_replay_typed=" evaluate_mk_apps_err_replay;
val _ = show_thm "dest_closure_none_apps_replay_typed=" dest_closure_none_apps_replay;
val _ = show_thm "evaluate_apps_long_replay_typed=" evaluate_apps_long_replay;
val _ = show_thm "evaluate_apps_timeout_replay_typed=" evaluate_apps_timeout_replay;
val _ = show_thm "evaluate_apps_timeout_alt_replay_typed=" evaluate_apps_timeout_alt_replay;
val _ = show_thm "evaluate_apps_short_replay_typed=" evaluate_apps_short_replay;
val _ = show_thm "state_rel_opt_rel_refs_replay_typed=" state_rel_opt_rel_refs_replay;
val _ = show_thm "rel_update_thunk_replay_typed=" rel_update_thunk_replay;
