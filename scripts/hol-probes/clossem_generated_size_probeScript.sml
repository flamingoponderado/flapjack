load "closSemTheory"; load "closLangTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "value_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closSemTheory.v_size_def); print "\n");
val _ = (print "exp_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.exp_size_def); print "\n");
val _ = (print "const_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.const_size_def); print "\n");
val _ = (print "const_part_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.const_part_size_def); print "\n");
val _ = (print "int_op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.int_op_size_def); print "\n");
val _ = (print "word_op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.word_op_size_def); print "\n");
val _ = (print "block_op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.block_op_size_def); print "\n");
val _ = (print "glob_op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.glob_op_size_def); print "\n");
val _ = (print "mem_op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.mem_op_size_def); print "\n");
val _ = (print "op_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl closLangTheory.op_size_def); print "\n");
val _ = (print "opw_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl (DB.fetch "backend_common" "opw_size_def")); print "\n");
val _ = (print "fp_cmp_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl (DB.fetch "fpSem" "fp_cmp_size_def")); print "\n");
val _ = (print "fp_uop_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl (DB.fetch "fpSem" "fp_uop_size_def")); print "\n");
val _ = (print "fp_bop_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl (DB.fetch "fpSem" "fp_bop_size_def")); print "\n");
val _ = (print "fp_top_size_type="; Lib.with_flag (Globals.show_types,true) print_term (concl (DB.fetch "fpSem" "fp_top_size_def")); print "\n");
val v_size_lemma_replay = prove
  (``MEM (v:closSem$v) vl ==> closSem$v_size v < closSem$v1_size vl``,
   Induct_on `vl` >> dsimp [closSemTheory.v_size_def] >> rpt strip_tac >>
   res_tac >> simp []);
val _ = (print "v_size_lemma_replay_type="; Lib.with_flag (Globals.show_types,true) print_term (concl v_size_lemma_replay); print "\n");
val _ = (print "block_example="; print_term (rhs (concl (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.w2n_n2w])) (EVAL ``closSem$v_size (closSem$Block 3 [closSem$Number 42; closSem$Word64 7w])``)))); print "\n");
val _ = (print "closure_example="; print_term (rhs (concl (EVAL ``closSem$v_size (closSem$Closure NONE [] [] 3 (closLang$Var backend_common$None 4))``))); print "\n");
val _ = (print "bytes_example="; print_term (rhs (concl (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.w2n_n2w])) (EVAL ``closSem$v_size (closSem$ByteVector [0w;255w;2w])``)))); print "\n");
val _ = (print "recclosure_example="; print_term (rhs (concl (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.w2n_n2w])) (EVAL ``closSem$v_size (closSem$Recclosure (SOME 2) [closSem$Number 1] [closSem$Word64 5w] [(1,closLang$Var backend_common$None 4)] 3)``)))); print "\n");
val _ = (print "op_example="; print_term (rhs (concl (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [wordsTheory.w2n_n2w])) (EVAL ``closLang$op_size (closLang$BlockOp (closLang$Constant (closLang$ConstCons 2 [closLang$ConstWord64 9w; closLang$ConstInt 4])))``)))); print "\n");
