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
val theorem_skip = GEN_ALL(Q.SPEC `panLang$Skip` compile_correct);
val _ = emit "compile_correct_skip_statement" theorem_skip;
val _ = print("compile_correct_skip_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_skip))) ^ "\n");
val theorem_break = GEN_ALL(Q.SPEC `panLang$Break` compile_correct);
val _ = emit "compile_correct_break_statement" theorem_break;
val _ = print("compile_correct_break_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_break))) ^ "\n");
val theorem_continue = GEN_ALL(Q.SPEC `panLang$Continue` compile_correct);
val _ = emit "compile_correct_continue_statement" theorem_continue;
val _ = print("compile_correct_continue_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_continue))) ^ "\n");
