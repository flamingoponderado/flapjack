load "preamble"; load "clos_mtiTheory"; load "closPropsTheory";
open HolKernel Parse bossLib preamble clos_mtiTheory closPropsTheory;
val _ = new_theory "flapjack_clos_mti_collect_args_replay";
val _ = Globals.linewidth := 1000000;

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

fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "mk_fns_def_typed" mk_Fns_def;
val _ = show "collect_args_def_typed" collect_args_def;
val _ = show "collect_args_imp_typed" collect_args_IMP;
val _ = show "collect_args_ok_imp_typed" collect_args_ok_IMP;
