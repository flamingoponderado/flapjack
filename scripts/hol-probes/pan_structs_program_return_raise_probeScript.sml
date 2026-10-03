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
val theorem_return = GEN_ALL(Q.SPEC `panLang$Return expression` compile_correct);
val _ = emit "compile_correct_return_statement" theorem_return;
val _ = print("compile_correct_return_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_return))) ^ "\n");
val theorem_raise = GEN_ALL(Q.SPEC `panLang$Raise exceptionId expression` compile_correct);
val _ = emit "compile_correct_raise_statement" theorem_raise;
val _ = print("compile_correct_raise_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_raise))) ^ "\n");
val _ = print("compile_correct_full_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_full)))) ^ "\n");
val _ = print("compile_correct_return_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_return)))) ^ "\n");
val _ = print("compile_correct_raise_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_raise)))) ^ "\n");
