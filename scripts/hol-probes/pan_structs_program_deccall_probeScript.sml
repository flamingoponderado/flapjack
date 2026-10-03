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
val theorem_deccall = GEN_ALL(Q.SPEC `panLang$DecCall v sh fnm es c1` compile_correct);
val _ = emit "compile_correct_deccall_statement" theorem_deccall;
val _ = print("compile_correct_deccall_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_deccall))) ^ "\n");
val _ = print("compile_correct_full_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_full)))) ^ "\n");
val _ = print("compile_correct_deccall_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_deccall)))) ^ "\n");
val theorem_ind = GEN_ALL panSemTheory.evaluate_ind;
val _ = emit "evaluate_ind_statement" theorem_ind;
val _ = print("evaluate_ind_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_ind))) ^ "\n");
val _ = print("evaluate_ind_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_ind)))) ^ "\n");
