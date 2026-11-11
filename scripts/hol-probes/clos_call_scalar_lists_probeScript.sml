load "clos_callProofTheory";
open HolKernel Parse boolLib bossLib closSemTheory clos_callProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val bytes = prove
 (``!x y c g code. v_rel c g code x y ==> !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=> (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw [] \\ fs [v_to_list_def,v_rel_def]
  \\ Cases_on `tag = cons_tag` \\ fs [] \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h'` \\ fs [v_rel_def] \\ Cases_on `h` \\ fs [v_rel_def]);
val _ = (print "bytes_replay="; Lib.with_flag (Globals.show_types,true) print_term (concl bytes); print "\n");
val words = prove
 (``!x y c g. v_rel c g code x y ==> !ns. (v_to_list x = SOME (MAP Word64 ns)) <=> (v_to_list y = SOME (MAP Word64 ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw [] \\ fs [v_to_list_def,v_rel_def]
  \\ Cases_on `tag = cons_tag` \\ fs [] \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h'` \\ fs [v_rel_def] \\ Cases_on `h` \\ fs [v_rel_def]);
val _ = (print "words_replay="; Lib.with_flag (Globals.show_types,true) print_term (concl words); print "\n");
