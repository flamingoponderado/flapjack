load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory;
val _ = Globals.linewidth := 1000000;
fun emit label th =
 (if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
  print(label ^ "="); print_term(concl th); print "\n");
val theorem_res_var_FMAP_MAP2_rev = GEN_ALL res_var_FMAP_MAP2_rev;
val _ = emit "res_var_FMAP_MAP2_rev_statement" theorem_res_var_FMAP_MAP2_rev;
val _ = print("res_var_FMAP_MAP2_rev_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_res_var_FMAP_MAP2_rev)))) ^ "\n");
val _ = print("res_var_FMAP_MAP2_rev_hypotheses=" ^ Int.toString(length(hyp theorem_res_var_FMAP_MAP2_rev)) ^ "\n");
val _ = print("res_var_FMAP_MAP2_rev_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_res_var_FMAP_MAP2_rev))) ^ "\n");
val theorem_FEVERY_res_var = GEN_ALL FEVERY_res_var;
val _ = emit "FEVERY_res_var_statement" theorem_FEVERY_res_var;
val _ = print("FEVERY_res_var_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_FEVERY_res_var)))) ^ "\n");
val _ = print("FEVERY_res_var_hypotheses=" ^ Int.toString(length(hyp theorem_FEVERY_res_var)) ^ "\n");
val _ = print("FEVERY_res_var_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_FEVERY_res_var))) ^ "\n");
