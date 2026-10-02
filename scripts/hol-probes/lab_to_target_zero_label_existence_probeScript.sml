load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val zero_labs_acc_of_eq_zero_labs_of = Q.prove (`domain (zero_labs_acc_of l acc) =
  IMAGE FST (restrict_zero (labs_of l)) ∪ domain acc`,
  Cases_on`l`>> (TRY (Cases_on`l'`))>>
  simp[backendPropsTheory.restrict_zero_def]>>
  rw[]>>
  simp[EXTENSION]);
val _=capture "zero_labs_acc_of_eq_zero_labs_of" zero_labs_acc_of_eq_zero_labs_of;
val _=types "zero_labs_acc_of_eq_zero_labs_of_types" zero_labs_acc_of_eq_zero_labs_of;
val _=print "zero_labs_acc_of_eq_zero_labs_of_hypotheses=";
val _=print(Int.toString(length(hyp zero_labs_acc_of_eq_zero_labs_of)) ^ "\n");
val line_get_zero_labs_acc_eq_line_get_zero_labels = Q.prove (`domain (line_get_zero_labs_acc l acc) =
  IMAGE FST (restrict_zero (line_get_labels l)) ∪ domain acc`,
  Cases_on`l`>>fs[line_get_zero_labs_acc_def,line_get_labels_def]>>
  simp[backendPropsTheory.restrict_zero_def]>>
  fs[zero_labs_acc_of_eq_zero_labs_of,backendPropsTheory.restrict_zero_def]);
val _=capture "line_get_zero_labs_acc_eq_line_get_zero_labels" line_get_zero_labs_acc_eq_line_get_zero_labels;
val _=types "line_get_zero_labs_acc_eq_line_get_zero_labels_types" line_get_zero_labs_acc_eq_line_get_zero_labels;
val _=print "line_get_zero_labs_acc_eq_line_get_zero_labels_hypotheses=";
val _=print(Int.toString(length(hyp line_get_zero_labs_acc_eq_line_get_zero_labels)) ^ "\n");
val sec_get_zero_labs_acc_eq_sec_get_zero_labels = Q.prove (`domain (sec_get_zero_labs_acc sec acc) =
  IMAGE FST (restrict_zero (sec_get_labels sec)) ∪ domain acc`,
  Cases_on`sec`>>Induct_on`l`>>
  fs[sec_get_zero_labs_acc_def,sec_get_labels_def]>>
  simp[line_get_zero_labs_acc_eq_line_get_zero_labels]>>
  simp[EXTENSION,backendPropsTheory.restrict_zero_def]>>
  metis_tac[]);
val _=capture "sec_get_zero_labs_acc_eq_sec_get_zero_labels" sec_get_zero_labs_acc_eq_sec_get_zero_labels;
val _=types "sec_get_zero_labs_acc_eq_sec_get_zero_labels_types" sec_get_zero_labs_acc_eq_sec_get_zero_labels;
val _=print "sec_get_zero_labs_acc_eq_sec_get_zero_labels_hypotheses=";
val _=print(Int.toString(length(hyp sec_get_zero_labs_acc_eq_sec_get_zero_labels)) ^ "\n");
val get_zero_labs_acc_eq_get_zero_labels = Q.prove (`domain (FOLDR sec_get_zero_labs_acc acc code) =
  IMAGE FST (restrict_zero (get_labels code)) ∪ domain acc`,
  Induct_on`code`>>fs[get_labels_def]>>
  simp[sec_get_zero_labs_acc_eq_sec_get_zero_labels]>>
  simp[EXTENSION,backendPropsTheory.restrict_zero_def]>>
  metis_tac[]);
val _=capture "get_zero_labs_acc_eq_get_zero_labels" get_zero_labs_acc_eq_get_zero_labels;
val _=types "get_zero_labs_acc_eq_get_zero_labels_types" get_zero_labs_acc_eq_get_zero_labels;
val _=print "get_zero_labs_acc_eq_get_zero_labels_hypotheses=";
val _=print(Int.toString(length(hyp get_zero_labs_acc_eq_get_zero_labels)) ^ "\n");
val zero_labs_acc_exist_eq = Q.prove (`zero_labs_acc_exist labs code ⇔
  restrict_zero (get_labels code) ⊆ labs_domain labs`,
  simp[zero_labs_acc_exist_def,EVERY_MEM,MEM_toAList,FORALL_PROD]>>
  `∀p. lookup p (get_zero_labs_acc code) = SOME () ⇔
    p ∈ domain (get_zero_labs_acc code)`
    by
    simp[domain_lookup]>>
  simp[get_zero_labs_acc_def,get_zero_labs_acc_eq_get_zero_labels]>>
  simp[labs_domain_def,lab_lookup_def]>>
  simp[SUBSET_DEF,EXISTS_PROD,FORALL_PROD]>>
  rw[EQ_IMP_THM]>>fs[backendPropsTheory.restrict_zero_def]>>
  rw[]>>
  first_x_assum old_drule>>fs[]>>
  every_case_tac>>fs[]);
val _=capture "zero_labs_acc_exist_eq" zero_labs_acc_exist_eq;
val _=types "zero_labs_acc_exist_eq_types" zero_labs_acc_exist_eq;
val _=print "zero_labs_acc_exist_eq_hypotheses=";
val _=print(Int.toString(length(hyp zero_labs_acc_exist_eq)) ^ "\n");

val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "zero_reference" ``lookup 7 (zero_labs_acc_of (Jump (Lab 7 0):8 asm_with_lab) (sptree$insert 42 () sptree$LN)) = SOME () /\ lookup 42 (zero_labs_acc_of (Jump (Lab 7 0):8 asm_with_lab) (sptree$insert 42 () sptree$LN)) = SOME ()``;
val _ = observe "nonzero_reference" ``zero_labs_acc_of (Jump (Lab 7 1):8 asm_with_lab) sptree$LN = sptree$LN``;
val _ = observe "call_ignored" ``zero_labs_acc_of (Call (Lab 7 0):8 asm_with_lab) sptree$LN = sptree$LN``;
val _ = observe "loc_reference" ``lookup 7 (zero_labs_acc_of (LocValue 9 (Lab 7 0):8 asm_with_lab) sptree$LN) = SOME ()``;
val _ = observe "empty_code" ``zero_labs_acc_exist (sptree$LN : bool num_map num_map) ([]:8 sec list)``;
val _ = observe "generic_value" ``zero_labs_acc_exist (sptree$insert 7 (sptree$insert 0 T sptree$LN) sptree$LN) ([Section 1 [LabAsm (Jump (Lab 7 0)) 0w [] 0]]:8 sec list)``;
val _ = observe "missing_outer" ``~zero_labs_acc_exist (sptree$LN : bool num_map num_map) ([Section 1 [LabAsm (Jump (Lab 7 0)) 0w [] 0]]:8 sec list)``;
val _ = observe "wrong_inner_key" ``~zero_labs_acc_exist (sptree$insert 7 (sptree$insert 1 T sptree$LN) sptree$LN) ([Section 1 [LabAsm (Jump (Lab 7 0)) 0w [] 0]]:8 sec list)``;
val _ = observe "width1" ``zero_labs_acc_exist (sptree$insert 7 (sptree$insert 0 T sptree$LN) sptree$LN) ([Section 1 [LabAsm (Jump (Lab 7 0)) 0w [] 0]]:1 sec list)``;
val _ = observe "width80_large_label" ``zero_labs_acc_exist (sptree$insert 1208925819614629174706176 (sptree$insert 0 F sptree$LN) sptree$LN) ([Section 1 [LabAsm (Jump (Lab 1208925819614629174706176 0)) 0w [] 0]]:80 sec list)``;
