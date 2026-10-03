load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stackSemTheory;
val _ = Globals.linewidth := 20000;
fun statement label th = print(label ^ "=" ^ term_to_string(concl th) ^ "\n");
fun types label th = print(label ^ "=" ^ String.concatWith ";" (map (fn v => fst(dest_var v) ^ type_to_string(type_of v)) (fst(strip_forall(concl th)))) ^ "\n");
fun proved label th = print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val su_setvar = prove(``!jump off k s t v x. state_rel jump off k s t /\ v < k ==> state_rel jump off k (set_var v x s) (set_var v x t)``,
  fs [state_rel_def,set_var_def] >> strip_tac >> simp [] >> fs [FLOOKUP_UPDATE] >> metis_tac []);
val _ = statement "su_setvar" su_setvar;
val _ = types "su_setvar_types" su_setvar;
val _ = proved "su_setvar_proved" su_setvar;
val su_getfp = prove(``!jump off k s t n. state_rel jump off k s t ==> get_fp_var n s = get_fp_var n t``,
  fs [state_rel_def,get_fp_var_def]);
val _ = statement "su_getfp" su_getfp;
val _ = types "su_getfp_types" su_getfp;
val _ = proved "su_getfp_proved" su_getfp;
val su_setfp = prove(``!jump off k s t n v. state_rel jump off k s t ==> state_rel jump off k (set_fp_var n v s) (set_fp_var n v t)``,
  rw [state_rel_def,set_fp_var_def] >> rfs [] >> res_tac >> fs []);
val _ = statement "su_setfp" su_setfp;
val _ = types "su_setfp_types" su_setfp;
val _ = proved "su_setfp_proved" su_setfp;
