load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory stackPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = numLib.temp_prefer_num();
fun theoremRow label th = (if null(hyp th) then () else raise Fail "open premise"; print(label ^ "="); print_thm th; print "\n");
val stack_move_no_labs = prove(``∀n a b c p.
  extract_labels p = [] ⇒
  extract_labels (stack_move n a b c p) = []``,
  Induct>>rw[stack_move_def]>>
  EVAL_TAC>>metis_tac[]);
val _ = theoremRow "elh_stack_move_no_labs" stack_move_no_labs;
val extract_labels_copy_ret_aux = prove(``∀k f n. extract_labels (copy_ret_aux k f n) = []``,
  ho_match_mp_tac copy_ret_aux_ind >>
  rw[]>>simp[Once copy_ret_aux_def]>>
  rw[]>>fs[extract_labels_def,stackLangTheory.list_Seq_def]);
val _ = theoremRow "elh_extract_labels_copy_ret_aux" extract_labels_copy_ret_aux;
val _ = augment_srw_ss [rewrites [extract_labels_copy_ret_aux]];
val extract_labels_copy_ret = prove(``extract_labels (copy_ret perf b kf vs kont) = extract_labels kont``,
  PairCases_on`kf`>>rw[copy_ret_def,extract_labels_def,SeqStackFree_def]);
val _ = theoremRow "elh_extract_labels_copy_ret" extract_labels_copy_ret;
val _ = augment_srw_ss [rewrites [extract_labels_copy_ret]];
val extract_labels_wStackLoad_Skip = prove(``extract_labels (wStackLoad xs Skip) = []``,
  Induct_on ‘xs’ >- EVAL_TAC
  >> rw []
  >> rename1 ‘x::xs’
  >> PairCases_on ‘x’
  >> simp [wStackLoad_def, extract_labels_def]);
val _ = theoremRow "elh_extract_labels_wStackLoad_Skip" extract_labels_wStackLoad_Skip;
val _ = augment_srw_ss [rewrites [extract_labels_wStackLoad_Skip]];
val extract_labels_stack_move_StackAlloc = prove(``∀n start offset i.
    extract_labels (stack_move n start offset i (StackAlloc k)) = []``,
  Induct >> rw []
  >- EVAL_TAC
  >> rw [stack_move_def, extract_labels_def]);
val _ = theoremRow "elh_extract_labels_stack_move_StackAlloc" extract_labels_stack_move_StackAlloc;
val _ = augment_srw_ss [rewrites [extract_labels_stack_move_StackAlloc]];
fun out label q = (print(label ^ "="); print_term(rhs(concl(EVAL q))); print "\n");
val _ = out "elh_1_move_0_skip" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Skip) : 1 stackLang$prog)``;
val _ = out "elh_1_move_0_labels" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_aux_0" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 0 : 1 stackLang$prog)``;
val _ = out "elh_1_alloc_0" ``stackProps$extract_labels (stack_move 0 0 9 4 (StackAlloc 1180591620717411303424) : 1 stackLang$prog)``;
val _ = out "elh_1_move_1_skip" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Skip) : 1 stackLang$prog)``;
val _ = out "elh_1_move_1_labels" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_aux_1" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 1 : 1 stackLang$prog)``;
val _ = out "elh_1_alloc_1" ``stackProps$extract_labels (stack_move 1 0 9 4 (StackAlloc 1180591620717411303424) : 1 stackLang$prog)``;
val _ = out "elh_1_move_3_skip" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Skip) : 1 stackLang$prog)``;
val _ = out "elh_1_move_3_labels" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_aux_3" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 3 : 1 stackLang$prog)``;
val _ = out "elh_1_alloc_3" ``stackProps$extract_labels (stack_move 3 0 9 4 (StackAlloc 1180591620717411303424) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_0_0" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_0_3" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_0_7" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_1_0" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_1_3" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_0_1_7" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_0_0" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_0_3" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_0_7" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_1_0" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_1_3" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_ret_1_1_7" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 1 stackLang$prog)``;
val _ = out "elh_1_load_24" ``stackProps$extract_labels (wStackLoad [] Skip : 1 stackLang$prog)``;
val _ = out "elh_1_load_25" ``stackProps$extract_labels (wStackLoad [(1,2)] Skip : 1 stackLang$prog)``;
val _ = out "elh_1_load_26" ``stackProps$extract_labels (wStackLoad [(1,2);(3,4);(1,2)] Skip : 1 stackLang$prog)``;
val _ = out "elh_8_move_0_skip" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Skip) : 8 stackLang$prog)``;
val _ = out "elh_8_move_0_labels" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_aux_0" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 0 : 8 stackLang$prog)``;
val _ = out "elh_8_alloc_0" ``stackProps$extract_labels (stack_move 0 0 9 4 (StackAlloc 1180591620717411303424) : 8 stackLang$prog)``;
val _ = out "elh_8_move_1_skip" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Skip) : 8 stackLang$prog)``;
val _ = out "elh_8_move_1_labels" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_aux_1" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 1 : 8 stackLang$prog)``;
val _ = out "elh_8_alloc_1" ``stackProps$extract_labels (stack_move 1 0 9 4 (StackAlloc 1180591620717411303424) : 8 stackLang$prog)``;
val _ = out "elh_8_move_3_skip" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Skip) : 8 stackLang$prog)``;
val _ = out "elh_8_move_3_labels" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_aux_3" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 3 : 8 stackLang$prog)``;
val _ = out "elh_8_alloc_3" ``stackProps$extract_labels (stack_move 3 0 9 4 (StackAlloc 1180591620717411303424) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_0_0" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_0_3" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_0_7" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_1_0" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_1_3" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_0_1_7" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_0_0" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_0_3" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_0_7" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_1_0" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_1_3" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_ret_1_1_7" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 8 stackLang$prog)``;
val _ = out "elh_8_load_51" ``stackProps$extract_labels (wStackLoad [] Skip : 8 stackLang$prog)``;
val _ = out "elh_8_load_52" ``stackProps$extract_labels (wStackLoad [(1,2)] Skip : 8 stackLang$prog)``;
val _ = out "elh_8_load_53" ``stackProps$extract_labels (wStackLoad [(1,2);(3,4);(1,2)] Skip : 8 stackLang$prog)``;
val _ = out "elh_64_move_0_skip" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Skip) : 64 stackLang$prog)``;
val _ = out "elh_64_move_0_labels" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_aux_0" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 0 : 64 stackLang$prog)``;
val _ = out "elh_64_alloc_0" ``stackProps$extract_labels (stack_move 0 0 9 4 (StackAlloc 1180591620717411303424) : 64 stackLang$prog)``;
val _ = out "elh_64_move_1_skip" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Skip) : 64 stackLang$prog)``;
val _ = out "elh_64_move_1_labels" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_aux_1" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 1 : 64 stackLang$prog)``;
val _ = out "elh_64_alloc_1" ``stackProps$extract_labels (stack_move 1 0 9 4 (StackAlloc 1180591620717411303424) : 64 stackLang$prog)``;
val _ = out "elh_64_move_3_skip" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Skip) : 64 stackLang$prog)``;
val _ = out "elh_64_move_3_labels" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_aux_3" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 3 : 64 stackLang$prog)``;
val _ = out "elh_64_alloc_3" ``stackProps$extract_labels (stack_move 3 0 9 4 (StackAlloc 1180591620717411303424) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_0_0" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_0_3" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_0_7" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_1_0" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_1_3" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_0_1_7" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_0_0" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_0_3" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_0_7" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_1_0" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_1_3" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_ret_1_1_7" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 64 stackLang$prog)``;
val _ = out "elh_64_load_78" ``stackProps$extract_labels (wStackLoad [] Skip : 64 stackLang$prog)``;
val _ = out "elh_64_load_79" ``stackProps$extract_labels (wStackLoad [(1,2)] Skip : 64 stackLang$prog)``;
val _ = out "elh_64_load_80" ``stackProps$extract_labels (wStackLoad [(1,2);(3,4);(1,2)] Skip : 64 stackLang$prog)``;
val _ = out "elh_80_move_0_skip" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Skip) : 80 stackLang$prog)``;
val _ = out "elh_80_move_0_labels" ``stackProps$extract_labels (stack_move 0 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_aux_0" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 0 : 80 stackLang$prog)``;
val _ = out "elh_80_alloc_0" ``stackProps$extract_labels (stack_move 0 0 9 4 (StackAlloc 1180591620717411303424) : 80 stackLang$prog)``;
val _ = out "elh_80_move_1_skip" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Skip) : 80 stackLang$prog)``;
val _ = out "elh_80_move_1_labels" ``stackProps$extract_labels (stack_move 1 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_aux_1" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 1 : 80 stackLang$prog)``;
val _ = out "elh_80_alloc_1" ``stackProps$extract_labels (stack_move 1 0 9 4 (StackAlloc 1180591620717411303424) : 80 stackLang$prog)``;
val _ = out "elh_80_move_3_skip" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Skip) : 80 stackLang$prog)``;
val _ = out "elh_80_move_3_labels" ``stackProps$extract_labels (stack_move 3 1180591620717411303424 9 4 (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_aux_3" ``stackProps$extract_labels (copy_ret_aux 4 1180591620717411303424 3 : 80 stackLang$prog)``;
val _ = out "elh_80_alloc_3" ``stackProps$extract_labels (stack_move 3 0 9 4 (StackAlloc 1180591620717411303424) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_0_0" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_0_3" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_0_7" ``stackProps$extract_labels (copy_ret F F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_1_0" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_1_3" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_0_1_7" ``stackProps$extract_labels (copy_ret F T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_0_0" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_0_3" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_0_7" ``stackProps$extract_labels (copy_ret T F (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_1_0" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_1_3" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_ret_1_1_7" ``stackProps$extract_labels (copy_ret T T (4,1180591620717411303424,0) [0;1;2;3;4;5;6] (Call (SOME (Skip,0,7,8)) (INR 0) (SOME (Skip,9,10))) : 80 stackLang$prog)``;
val _ = out "elh_80_load_105" ``stackProps$extract_labels (wStackLoad [] Skip : 80 stackLang$prog)``;
val _ = out "elh_80_load_106" ``stackProps$extract_labels (wStackLoad [(1,2)] Skip : 80 stackLang$prog)``;
val _ = out "elh_80_load_107" ``stackProps$extract_labels (wStackLoad [(1,2);(3,4);(1,2)] Skip : 80 stackLang$prog)``;
