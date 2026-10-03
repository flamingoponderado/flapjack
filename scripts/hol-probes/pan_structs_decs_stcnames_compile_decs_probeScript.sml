load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory panSemTheory;
val _ = Globals.linewidth := 1000000;
(* Original complete theorem1435 and unchanged proof; GEN_ALL closes free acc. *)
val original = GEN_ALL(prove(``!ctxt decs.
  decs_stcnames acc (FST(compile_decs ctxt decs)) = SOME acc``,
  recInduct compile_decs_ind >> simp [compile_decs_def,decs_stcnames_def]
  >> rw [] >> rpt(pairarg_tac >> fs []) >> fs [decs_stcnames_def]));
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "decs_stcnames_compile_decs_statement="; print_term(concl original); print "\n");
val _ = print("decs_stcnames_compile_decs_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("decs_stcnames_compile_decs_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
