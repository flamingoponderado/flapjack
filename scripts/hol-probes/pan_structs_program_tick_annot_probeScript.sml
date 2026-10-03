load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory panLangTheory;
val _ = Globals.linewidth := 1000000;
fun emit label th =
 (if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
  print(label ^ "="); print_term(concl th); print "\n");
val theorem_full = GEN_ALL compile_correct;
val _ = emit "compile_correct_full_statement" theorem_full;
val _ = print("compile_correct_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_full))) ^ "\n");
val theorem_tick = GEN_ALL(Q.SPEC `panLang$Tick` compile_correct);
val _ = emit "compile_correct_tick_statement" theorem_tick;
val _ = print("compile_correct_tick_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_tick))) ^ "\n");
val theorem_annot = GEN_ALL(Q.SPEC `panLang$Annot tag text` compile_correct);
val _ = emit "compile_correct_annot_statement" theorem_annot;
val _ = print("compile_correct_annot_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_annot))) ^ "\n");
