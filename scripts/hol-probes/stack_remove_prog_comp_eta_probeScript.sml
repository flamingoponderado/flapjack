load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory stack_removeTheory;
val _ = Globals.linewidth := 20000;
val prog_comp_eta_replay = prove(``prog_comp = \jump off k (n,p). (n,comp jump off k p)``,
  srw_tac[][FUN_EQ_THM,prog_comp_def,FORALL_PROD,LAMBDA_PROD]);
val _ = print("prog_comp_eta_statement=" ^ term_to_string(concl prog_comp_eta_replay) ^ "\n");
val _ = print("prog_comp_eta_proved=" ^ term_to_string(rhs(concl(EQT_INTRO prog_comp_eta_replay))) ^ "\n");
