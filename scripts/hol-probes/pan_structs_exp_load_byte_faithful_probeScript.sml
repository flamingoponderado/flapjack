load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory panLangTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL compile_exp_correct;
val load_byte_case = GEN_ALL(Q.SPEC `panLang$LoadByte expression` (Q.SPEC `s` compile_exp_correct));
fun emit label th =
  (if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
   print(label ^ "="); print_term(concl th); print "\n");
val _ = emit "compile_exp_correct_full_statement" original;
val _ = print("compile_exp_correct_full_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = emit "compile_exp_correct_load_byte_statement" load_byte_case;
val _ = print("compile_exp_correct_load_byte_proved=" ^ term_to_string(rhs(concl(EQT_INTRO load_byte_case))) ^ "\n");
val _ = emit "eval_ind_full_statement" (GEN_ALL panSemTheory.eval_ind);
