(* Independent review of canonical 8e43beee1. Run from the read-only
   cakeml/compiler/backend/reg_alloc theory directory with HOL/bin/hol run
   and this script absolute path. Loads original prebuilt parmoveTheory;
   exports no theory and writes no source artifacts. Finite boundary checks
   are regression evidence, not cross-prover equivalence. *)
load "preamble"; load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
val _ = print_thm (DB.fetch "parmove" "inj_on_state_def");
val _ = print_type (type_of ``inj_on_state``);

fun observe label term = (print (label ^ "="); print_term (rhs(concl(SIMP_CONV (srw_ss()) [inj_on_state_def,state_to_list_def,optionTheory.FORALL_OPTION,boolTheory.FORALL_BOOL,boolTheory.LET_DEF] term))); print "\n");
val _ = observe "inj_support" ``inj_on_state (\x:bool option. case x of NONE => NONE | SOME b => SOME ()) ([(SOME F,SOME F)],[],[])``;
val _ = observe "inj_pending_collision" ``inj_on_state (\x:bool option. case x of NONE => NONE | SOME b => SOME ()) ([(SOME F,SOME T)],[],[])``;
val _ = observe "inj_active_collision" ``inj_on_state (\x:bool option. case x of NONE => NONE | SOME b => SOME ()) ([],[(SOME F,SOME T)],[])``;
val _ = observe "inj_emitted_collision" ``inj_on_state (\x:bool option. case x of NONE => NONE | SOME b => SOME ()) ([],[],[(SOME F,SOME T)])``;

val _ = observe "inj_none_empty" ``inj_on_state (\x:bool option. NONE:unit option) ([],[],[])``;
val _ = observe "inj_some_empty" ``inj_on_state (\x:bool option. SOME ()) ([],[],[])``;
