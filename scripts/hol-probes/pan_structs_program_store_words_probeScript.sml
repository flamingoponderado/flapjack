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
val theorem_store32 = GEN_ALL(Q.SPEC `panLang$Store32 e1 e2` compile_correct);
val _ = emit "compile_correct_store32_statement" theorem_store32;
val _ = print("compile_correct_store32_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_store32))) ^ "\n");
val theorem_store_byte = GEN_ALL(Q.SPEC `panLang$StoreByte e1 e2` compile_correct);
val _ = emit "compile_correct_store_byte_statement" theorem_store_byte;
val _ = print("compile_correct_store_byte_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_store_byte))) ^ "\n");
val _ = print("compile_correct_full_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_full)))) ^ "\n");
val _ = print("compile_correct_store32_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_store32)))) ^ "\n");
val _ = print("compile_correct_store_byte_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_store_byte)))) ^ "\n");
