(* Literal local HOL theorem replay. Independent carriers are captured from
   HOL inference; this regression is not a cross-language equivalence proof. *)
load "bossLib"; load "preamble"; load "word_to_wordProofTheory";
open HolKernel Parse bossLib preamble wordSemTheory word_to_wordTheory sptreeTheory;
val source_cake = valOf (OS.Process.getEnv "CAKEML");
val stream = TextIO.openIn (OS.Path.concat(source_cake,
  "compiler/backend/proofs/word_to_wordProofScript.sml"));
val source = TextIO.inputAll stream;
val _ = TextIO.closeIn stream;
val _ = if String.isSubstring "Theorem find_code_thm[local]:\n  (!n v. lookup n st.code = SOME v ==>\n         ∃t k a c col.\n         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧\n  find_code o1 (add_ret_loc o' x) st.code st.stack_size = SOME (args,prog, locsize) ⇒\n  ∃t k a c col n prog'.\n  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧\n  find_code o1 (add_ret_loc o' x) l st.stack_size = SOME(args,prog', locsize)\nProof\n  Cases_on`o1`>>simp[find_code_def]>>srw_tac[][]\n  >-\n    (ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>\n    Cases_on`lookup n st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>\n    Cases_on`x'`>> full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>\n    qsuff_tac`q = LENGTH args`>-\n     metis_tac[]>>\n    qpat_x_assum`A=args` sym_sub_tac>>\n    Cases_on`add_ret_loc o' x`>>full_simp_tac(srw_ss())[LENGTH_FRONT,ADD1])\n  >>\n    Cases_on`lookup x' st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>\n    Cases_on`x''`>>full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>\n    metis_tac[]\nQED" source then ()
  else raise Fail "find_code_thm original source changed";
val _ = new_theory "flapjack_find_code_carriers_replay";
val replay = store_thm("find_code_carriers_replay",
``  (!n v. lookup n st.code = SOME v ==>
         ∃t k a c col.
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧
  find_code o1 (add_ret_loc o' x) st.code st.stack_size = SOME (args,prog, locsize) ⇒
  ∃t k a c col n prog'.
  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧
  find_code o1 (add_ret_loc o' x) l st.stack_size = SOME(args,prog', locsize)``,
  Cases_on`o1`>>simp[find_code_def]>>srw_tac[][]
  >-
    (ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`lookup n st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>
    Cases_on`x'`>> full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>
    qsuff_tac`q = LENGTH args`>-
     metis_tac[]>>
    qpat_x_assum`A=args` sym_sub_tac>>
    Cases_on`add_ret_loc o' x`>>full_simp_tac(srw_ss())[LENGTH_FRONT,ADD1])
  >>
    Cases_on`lookup x' st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>
    metis_tac[]);
val _ = Globals.linewidth := 1000000;
val _ = print "find_code_independent_carriers_typed=";
val _ = Lib.with_flag (Globals.show_types, true) print_term (concl replay);
val _ = print "\n";
val _ = print ("find_code_independent_carriers_hypotheses=" ^
  Int.toString (length (hyp replay)) ^ "\n");
