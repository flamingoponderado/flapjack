load "preamble"; load "miscTheory"; load "alignmentTheory"; load "data_to_word_gcProofTheory";
open HolKernel Parse bossLib preamble miscTheory alignmentTheory;
val _ = new_theory "flapjack_pan_target_root_leaves_replay";
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (miscTheory.UPDATE_LIST_def)) then () else raise Fail "hypotheses: UPDATE_LIST_def";
val _ = (print "UPDATE_LIST_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.UPDATE_LIST_def)); print "\n");
val _ = if null (hyp (miscTheory.APPLY_UPDATE_LIST_ALOOKUP)) then () else raise Fail "hypotheses: APPLY_UPDATE_LIST_ALOOKUP";
val _ = (print "APPLY_UPDATE_LIST_ALOOKUP_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.APPLY_UPDATE_LIST_ALOOKUP)); print "\n");
val _ = if null (hyp (miscTheory.MOD_SUB_LEMMA)) then () else raise Fail "hypotheses: MOD_SUB_LEMMA";
val _ = (print "MOD_SUB_LEMMA_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.MOD_SUB_LEMMA)); print "\n");
val _ = if null (hyp (miscTheory.DISJOINT_INTER)) then () else raise Fail "hypotheses: DISJOINT_INTER";
val _ = (print "DISJOINT_INTER_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.DISJOINT_INTER)); print "\n");
val _ = if null (hyp (miscTheory.IMP_MULT_DIV_LESS)) then () else raise Fail "hypotheses: IMP_MULT_DIV_LESS";
val _ = (print "IMP_MULT_DIV_LESS_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.IMP_MULT_DIV_LESS)); print "\n");
val _ = if null (hyp (miscTheory.DIV_LESS_DIV)) then () else raise Fail "hypotheses: DIV_LESS_DIV";
val _ = (print "DIV_LESS_DIV_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.DIV_LESS_DIV)); print "\n");
val _ = if null (hyp (miscTheory.WORD_LS_IMP)) then () else raise Fail "hypotheses: WORD_LS_IMP";
val _ = (print "WORD_LS_IMP_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (miscTheory.WORD_LS_IMP)); print "\n");
val _ = if null (hyp (data_to_word_gcProofTheory.lsr_lsl)) then () else raise Fail "hypotheses: lsr_lsl";
val _ = (print "lsr_lsl_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (data_to_word_gcProofTheory.lsr_lsl)); print "\n");
(* Literal source replay of backendProofScript 29-37 (backendProofTheory is not built here). *)
Theorem byte_aligned_mult:
   good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)
Proof
  fs [alignmentTheory.byte_aligned_def,good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``), aligned_add_pow]
QED
val _ = if null (hyp (byte_aligned_mult)) then () else raise Fail "hypotheses: byte_aligned_mult";
val _ = (print "byte_aligned_mult_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (byte_aligned_mult)); print "\n");
