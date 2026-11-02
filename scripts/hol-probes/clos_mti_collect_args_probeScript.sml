load "preamble"; load "clos_mtiTheory"; load "closPropsTheory";
load "clos_mtiProofTheory";
open HolKernel Parse bossLib preamble clos_mtiTheory closPropsTheory;
val _ = new_theory "flapjack_clos_mti_collect_args_replay";
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
fun bring_fwd_ctors th ty = map ((fn s => Parse.bring_to_front_overload s {Name = s, Thy = th}) o term_to_string) (TypeBase.constructors_of ty);
val _ = bring_fwd_ctors "closLang" ``:closLang$exp``;

(* Literal replays of clos_mtiProofScript.sml:63-66 and 177-201. *)
Definition mk_Fns_def:
  mk_Fns [] e = e /\
  mk_Fns (t::ts) e = Fn t NONE NONE 1 (mk_Fns ts e)
End

Theorem collect_args_IMP:
   !max_app k e1 num_args e2.
      collect_args max_app k e1 = (num_args,e2) /\ k <= max_app ==>
      k <= num_args /\ num_args <= max_app
Proof
  recInduct collect_args_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ fs [collect_args_def]
  \\ rw [] \\ fs []
QED

Theorem collect_args_ok_IMP:
   !max_app k e num_args e2.
      collect_args max_app k e = (num_args,e2) /\ no_mti e ==>
      ?ts. e = mk_Fns ts e2 /\ num_args = k + LENGTH ts /\ no_mti e2
Proof
  recInduct collect_args_ind
  \\ rw [] \\ fs []
  \\ fs [collect_args_def] \\ rveq
  \\ TRY (fs [collect_args_def] \\ rveq
          \\ qexists_tac `[]` \\ fs [mk_Fns_def] \\ NO_TAC)
  \\ NORM_TAC (srw_ss()) []
  \\ gvs [no_mti_def,mk_Fns_def]
  \\ qexists_tac `t::ts` \\ rw [mk_Fns_def]
QED

Theorem collect_apps_acc:
    !max_app acc e res s.
      collect_apps max_app acc e = (res,s) ==>
      ?other. res = acc ++ other
Proof
  recInduct collect_apps_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [collect_apps_def]
  \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem collect_apps_cons_lemma:
    !e1 m ys other e2.
      collect_apps (m+LENGTH ys) ys e1 = (ys ++ other,e2) <=>
      collect_apps m [] e1 = (other,e2)
Proof
  Induct \\ fs [collect_apps_def]
  \\ rw [] \\ Cases_on `o'` \\ fs [collect_apps_def]
  \\ rw [] \\ fs []
  \\ fs [LESS_EQ_EXISTS]
  \\ Cases_on `collect_apps (p + LENGTH l) l e1`
  \\ drule collect_apps_acc
  \\ strip_tac \\ rveq \\ fs []
  \\ Cases_on `collect_apps (p + (LENGTH l + LENGTH ys)) (ys ++ l) e1`
  \\ drule collect_apps_acc
  \\ strip_tac \\ rveq \\ fs []
  \\ pop_assum mp_tac
  \\ `(LENGTH l + LENGTH ys) = LENGTH (ys ++ l)` by fs []
  \\ asm_rewrite_tac []
  \\ rfs []
QED

Theorem collect_apps_cons:
    !e1 m x other e2.
      collect_apps m [x] e1 = (x::other,e2) /\ m <> 0 ==>
      collect_apps (m-1) [] e1 = (other,e2)
Proof
  once_rewrite_tac [collect_apps_cons_lemma |> GSYM
       |> Q.SPECL [`e1`,`m`,`[x]`]
       |> SIMP_RULE std_ss [LENGTH,APPEND]] \\ rw []
QED

Definition mk_Apps_def:
  mk_Apps e [] = e /\
  mk_Apps e ((t,other)::ts) = App t NONE (mk_Apps e ts) [other]
End

Theorem collect_apps_IMP_mk_Apps:
  !e max_app (acc:closLang$exp list) other e3.
      collect_apps max_app [] e = (other,e3) /\ no_mti e ==>
      ?ts. e = mk_Apps e3 (ZIP (ts, other)) /\ LENGTH other = LENGTH ts /\
           LENGTH other <= max_app
Proof
  Induct \\ fs [] \\ rw []
  \\ fs [collect_apps_def] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def]
          \\ FULL_CASE_TAC \\ fs [] \\ rveq \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [no_mti_def] \\ rveq
  \\ fs [collect_apps_def] \\ rveq
  \\ FULL_CASE_TAC \\ fs [] \\ rveq
  \\ TRY (qexists_tac `[]` \\ fs [mk_Apps_def] \\ NO_TAC)
  \\ fs [no_mti_def]
  \\ imp_res_tac collect_apps_acc \\ rveq \\ fs []
  \\ Cases_on `l` \\ gvs []
  \\ drule (GEN_ALL collect_apps_cons) \\ fs []
  \\ strip_tac \\ first_x_assum drule
  \\ strip_tac \\ rveq \\ fs []
  \\ qexists_tac `t::ts` \\ fs [ZIP,mk_Apps_def]
QED

Theorem collect_apps_no_mti:
   !k aux e res e1.
      collect_apps k aux e = (res,e1) /\
      no_mti e /\ EVERY no_mti aux ==>
      EVERY no_mti res /\ no_mti e1
Proof
  recInduct collect_apps_ind
  \\ rw [collect_apps_def] \\ fs []
  \\ fs [no_mti_def, ETA_THM]
QED

(* Literal replay of closPropsScript.sml:2165-2185, which is local in HOL. *)
val case_eq_thms = pair_case_eq::bool_case_eq::list_case_eq::option_case_eq::map TypeBase.case_eq_of
  [``:'a ffi_result``, ``:v``, ``:'a ref``, ``:closLang$op``, ``:closLang$mem_op``,
   ``:closLang$int_op``, ``:closLang$word_op``, ``:closLang$block_op``, ``:closLang$glob_op``,
   ``:word_size``, ``:eq_result``, ``:('a,'b) result``, ``:'a error_result``, ``:app_kind``]
  |> LIST_CONJ;
Theorem v_rel_do_eq_replay:
    simple_val_rel vr ==>
    (!y1 y2 x1 x2.
      vr x1 y1 /\ vr x2 y2 ==>
      do_eq x1 x2 = do_eq y1 y2) /\
    (!y1 y2 x1 x2.
      LIST_REL vr x1 y1 /\ LIST_REL vr x2 y2 ==>
      do_eq_list x1 x2 = do_eq_list y1 y2)
Proof
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac closSemTheory.do_eq_ind \\ rw []
  THEN1
   (Cases_on `y1` \\ fs [] \\ rfs [] \\ rveq \\ fs []
    \\ Cases_on `y2` \\ rfs [closSemTheory.do_eq_def]
    \\ res_tac \\ fs [isClos_cases]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ once_rewrite_tac [closSemTheory.do_eq_def]
  \\ fs [case_eq_thms]
  \\ Cases_on `do_eq y1 y2` \\ fs []
  \\ Cases_on `b` \\ fs []
QED

fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "mk_fns_def_typed" mk_Fns_def;
val _ = show "collect_args_def_typed" collect_args_def;
val _ = show "collect_args_imp_typed" collect_args_IMP;
val _ = show "collect_args_ok_imp_typed" collect_args_ok_IMP;
val _ = show "collect_apps_def_typed" collect_apps_def;
val _ = show "collect_apps_acc_typed" collect_apps_acc;
val _ = show "collect_apps_cons_lemma_typed" collect_apps_cons_lemma;
val _ = show "collect_apps_cons_typed" collect_apps_cons;
val _ = show "mk_apps_def_typed" mk_Apps_def;
val _ = show "collect_apps_rebuild_typed" collect_apps_IMP_mk_Apps;
val _ = show "collect_apps_no_mti_typed" collect_apps_no_mti;
val _ = show "intro_multi_def_typed" clos_mtiTheory.intro_multi_def;
val _ = show "intro_multi_length_typed" clos_mtiTheory.intro_multi_length;
val _ = show "intro_multi_sing_typed" clos_mtiTheory.intro_multi_sing;
val _ = show "code_rel_typed" clos_mtiProofTheory.code_rel_def;
val _ = show "code_rel_length_typed" clos_mtiProofTheory.code_rel_IMP_LENGTH;
val _ = show "function_rel_typed" clos_mtiProofTheory.f_rel_def;
val _ = show "value_rel_rules_typed" clos_mtiProofTheory.v_rel_rules;
val _ = show "value_rel_opt_typed" clos_mtiProofTheory.v_rel_opt_def;
val _ = show "ref_rel_rules_typed" clos_mtiProofTheory.ref_rel_rules;
val _ = show "compile_typed" clos_mtiTheory.compile_def;
val _ = show "compile_inc_typed" clos_mtiTheory.compile_inc_def;
val _ = show "conditional_compile_inc_typed" clos_mtiTheory.cond_mti_compile_inc_def;
val _ = show "snd_compile_inc_typed" clos_mtiProofTheory.SND_compile_inc;
val _ = show "fmap_rel_typed" clos_mtiProofTheory.FMAP_REL_def;
val _ = show "state_rel_typed" clos_mtiProofTheory.state_rel_def;
val _ = show "is_closure_typed" closPropsTheory.isClos_def;
val _ = show "simple_value_relation_typed" closPropsTheory.simple_val_rel_def;
val _ = show "mti_simple_value_relation_typed" clos_mtiProofTheory.simple_val_rel;
val _ = show "simple_state_relation_typed" closPropsTheory.simple_state_rel_def;
val _ = show "mti_simple_state_relation_typed" clos_mtiProofTheory.simple_state_rel;
val _ = show "vr_list_to_value_typed" closPropsTheory.vr_list_to_v;
val _ = show "vr_list_none_typed" closPropsTheory.vr_list_NONE;
val _ = show "simple_value_append_typed" closPropsTheory.simple_val_rel_APPEND;
val _ = show "list_to_value_inj_typed" closPropsTheory.list_to_v_INJ;
val _ = show "simple_value_list_typed" closPropsTheory.simple_val_rel_list;
val _ = show "value_equality_relation_typed" v_rel_do_eq_replay;
