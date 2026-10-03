load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val t = DB.fetch "lab_to_targetProof" "compiler_oracle_ok_def";
val _ = capture "compiler_oracle_ok_def" t;
val _ = types "compiler_oracle_ok_def_types" t;
val _ = print("compiler_oracle_ok_def_hypotheses=" ^ Int.toString(length(hyp t)) ^ "\n");
val _ = show_types := false;
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO th))); print "\n");
val _ = checked "full_contract" (prove(
  ``compiler_oracle_ok coracle init_labs init_pos c ffis <=>
    (!k. good_code c (FST (coracle k)).labels (SND (coracle k)) /\
      labProps$no_share_mem_inst (SND (coracle k))) /\
    ((FST (coracle 0)).labels = init_labs /\
      (FST (coracle 0)).pos = init_pos /\
      (FST (coracle 0)).ffi_names = SOME ffis)``,
  simp [compiler_oracle_ok_def, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >> metis_tac []));
val _ = checked "all_good_code" (prove(
  ``compiler_oracle_ok coracle init_labs init_pos c ffis ==>
    !k. good_code c (FST (coracle k)).labels (SND (coracle k))``,
  simp [compiler_oracle_ok_def, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >> metis_tac []));
val _ = checked "all_no_share_mem" (prove(
  ``compiler_oracle_ok coracle init_labs init_pos c ffis ==>
    !k. labProps$no_share_mem_inst (SND (coracle k))``,
  simp [compiler_oracle_ok_def, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >> metis_tac []));
val _ = checked "zero_config" (prove(
  ``compiler_oracle_ok coracle init_labs init_pos c ffis ==>
    (FST (coracle 0)).labels = init_labs /\
    (FST (coracle 0)).pos = init_pos /\
    (FST (coracle 0)).ffi_names = SOME ffis``,
  simp [compiler_oracle_ok_def, pairTheory.pair_CASE_def, pairTheory.UNCURRY] >> metis_tac []));
