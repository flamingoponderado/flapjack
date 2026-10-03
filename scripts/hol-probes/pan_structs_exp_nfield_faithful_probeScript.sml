load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsTheory pan_structsProofTheory panLangTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL compile_exp_correct;
val nfield_case = GEN_ALL(Q.SPEC `panLang$NField fld expression` (Q.SPEC `s` compile_exp_correct));
fun emit label th =
  (if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
   print(label ^ "="); print_term(concl th); print "\n");
val _ = emit "compile_exp_correct_full_statement" original;
val _ = print("compile_exp_correct_full_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = emit "compile_exp_correct_nfield_statement" nfield_case;
val _ = print("compile_exp_correct_nfield_proved=" ^ term_to_string(rhs(concl(EQT_INTRO nfield_case))) ^ "\n");
val _ = emit "eval_ind_full_statement" (GEN_ALL panSemTheory.eval_ind);
