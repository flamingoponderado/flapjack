load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
(* Original local theorem and unchanged proof, pan_structsProofScript1346-1355. *)
val original = prove(``!ctxt decs decs' ctxt'.
  compile_decs ctxt decs = (decs',ctxt') ==> ctxt'.structs = ctxt.structs``,
  recInduct compile_decs_ind >> simp [compile_decs_def] >> rw [] >> fs [UNCURRY_EQ]);
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "compile_decs_structs_statement="; print_term(concl original); print "\n");
val _ = print("compile_decs_structs_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("compile_decs_structs_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
