(* Literal original local statements AND proofs, replayed over pinned theories.
   The two restriction instances replay the original derivations. This does not
   establish HOL-to-Lean equivalence. *)
load "bossLib"; load "preamble"; load "word_to_wordProofTheory";
load "wordConvsTheory"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble wordSemTheory word_to_wordTheory
  word_to_wordProofTheory wordConvsTheory wordPropsTheory sptreeTheory;
val source_cake = valOf (OS.Process.getEnv "CAKEML");
val stream = TextIO.openIn (OS.Path.concat(source_cake,
  "compiler/backend/proofs/word_to_wordProofScript.sml"));
val source = TextIO.inputAll stream;
val _ = TextIO.closeIn stream;
val _ = new_theory "flapjack_word_to_word_locals_replay";
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 1000000;
fun emit label th = (print(label ^ "="); print_term(concl th); print "\n");
fun hyps label th = print(label ^ "=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = if String.isSubstring "Theorem rm_perm[local]:\n  s with permute:= s.permute = s\nProof\n  full_simp_tac(srw_ss())[state_component_equality]\nQED" source then () else raise Fail "rm_perm source changed";
val rm_perm = store_thm("rm_perm_replay",
``  s with permute:= s.permute = s``,
  full_simp_tac(srw_ss())[state_component_equality]);
val _ = if String.isSubstring "Theorem find_code_thm[local]:\n  (!n v. lookup n st.code = SOME v ==>\n         ∃t k a c col.\n         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ∧\n  find_code o1 (add_ret_loc o' x) st.code st.stack_size = SOME (args,prog, locsize) ⇒\n  ∃t k a c col n prog'.\n  SND(compile_single t k a c ((n,LENGTH args,prog),col)) = (LENGTH args,prog') ∧\n  find_code o1 (add_ret_loc o' x) l st.stack_size = SOME(args,prog', locsize)\nProof\n  Cases_on`o1`>>simp[find_code_def]>>srw_tac[][]\n  >-\n    (ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>\n    Cases_on`lookup n st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>\n    Cases_on`x'`>> full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>\n    qsuff_tac`q = LENGTH args`>-\n     metis_tac[]>>\n    qpat_x_assum`A=args` sym_sub_tac>>\n    Cases_on`add_ret_loc o' x`>>full_simp_tac(srw_ss())[LENGTH_FRONT,ADD1])\n  >>\n    Cases_on`lookup x' st.code`>>full_simp_tac(srw_ss())[]>>res_tac>>\n    Cases_on`x''`>>full_simp_tac(srw_ss())[compile_single_def,LET_THM]>>\n    metis_tac[]\nQED" source then () else raise Fail "find_code_thm source changed";
val find_code_thm = store_thm("find_code_thm_replay",
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
val _ = if String.isSubstring "Theorem pop_env_termdep[local]:\n  pop_env rst = SOME x ⇒ x.termdep = rst.termdep\nProof\n  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality]\nQED" source then () else raise Fail "pop_env_termdep source changed";
val pop_env_termdep = store_thm("pop_env_termdep_replay",
``  pop_env rst = SOME x ⇒ x.termdep = rst.termdep``,
  full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality]);
val _ = if String.isSubstring "Theorem compile_single_eta[local]:\n  compile_single t k a c ((p,x),y) =\n  (p,SND (compile_single t k a c ((p,x),y)))\nProof\n  Cases_on`x`>>fs[compile_single_def]\nQED" source then () else raise Fail "compile_single_eta source changed";
val compile_single_eta = store_thm("compile_single_eta_replay",
``  compile_single t k a c ((p,x),y) =
  (p,SND (compile_single t k a c ((p,x),y)))``,
  Cases_on`x`>>fs[compile_single_def]);
val _ = if String.isSubstring "Theorem code_rel_union_fromAList[local]:\n  ∀s l ls.\n  code_rel s l ∧\n  domain s = domain l\n  ⇒\n  code_rel (union s (fromAList ls)) (union l (fromAList (MAP (λp. compile_single t k a c (p,NONE)) ls)))\nProof\n  rw[code_rel_def]>>\n  fs[lookup_union,case_eq_thms]\n  >-\n    (`lookup n l = NONE` by\n      (fs[EXTENSION,domain_lookup]>>\n      metis_tac[option_CLAUSES])>>\n    fs[lookup_fromAList]>>\n    simp[Once LAMBDA_PROD,Once compile_single_eta]>>\n    simp[ALOOKUP_MAP_2]>>\n    metis_tac[])\n  >>\n    first_x_assum old_drule>>rw[]>>\n    simp[]>>metis_tac[]\nQED" source then () else raise Fail "code_rel_union_fromAList source changed";
val code_rel_union_fromAList = store_thm("code_rel_union_fromAList_replay",
``  ∀s l ls.
  code_rel s l ∧
  domain s = domain l
  ⇒
  code_rel (union s (fromAList ls)) (union l (fromAList (MAP (λp. compile_single t k a c (p,NONE)) ls)))``,
  rw[code_rel_def]>>
  fs[lookup_union,case_eq_thms]
  >-
    (`lookup n l = NONE` by
      (fs[EXTENSION,domain_lookup]>>
      metis_tac[option_CLAUSES])>>
    fs[lookup_fromAList]>>
    simp[Once LAMBDA_PROD,Once compile_single_eta]>>
    simp[ALOOKUP_MAP_2]>>
    metis_tac[])
  >>
    first_x_assum old_drule>>rw[]>>
    simp[]>>metis_tac[]);
val _ = if String.isSubstring "Theorem code_rel_P[local] = Q.GEN `P` code_rel_not_created_subprogs;\n\nTheorem code_rel_no_alloc[local] = code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))`\n    |> REWRITE_RULE [GSYM no_alloc_subprogs_def]\n\nTheorem code_rel_no_install[local] = code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))`\n    |> REWRITE_RULE [GSYM no_install_subprogs_def]" source then () else raise Fail "restriction instances source changed";
val code_rel_P = Q.GEN `P` code_rel_not_created_subprogs;
val code_rel_no_alloc = code_rel_P |> Q.SPEC `(<>) (Alloc 0 (LN,LN))`
    |> REWRITE_RULE [GSYM no_alloc_subprogs_def];
val code_rel_no_install = code_rel_P |> Q.SPEC `(<>) (Install 0 0 0 0 (LN,LN))`
    |> REWRITE_RULE [GSYM no_install_subprogs_def];
val _ = emit "rm_perm_statement" rm_perm;
val _ = hyps "rm_perm_hypotheses" rm_perm;
val _ = emit "find_code_thm_statement" find_code_thm;
val _ = hyps "find_code_thm_hypotheses" find_code_thm;
val _ = emit "pop_env_termdep_statement" pop_env_termdep;
val _ = hyps "pop_env_termdep_hypotheses" pop_env_termdep;
val _ = emit "compile_single_eta_statement" compile_single_eta;
val _ = hyps "compile_single_eta_hypotheses" compile_single_eta;
val _ = emit "code_rel_union_fromAList_statement" code_rel_union_fromAList;
val _ = hyps "code_rel_union_fromAList_hypotheses" code_rel_union_fromAList;
val _ = emit "code_rel_no_alloc_statement" code_rel_no_alloc;
val _ = hyps "code_rel_no_alloc_hypotheses" code_rel_no_alloc;
val _ = emit "code_rel_no_install_statement" code_rel_no_install;
val _ = hyps "code_rel_no_install_hypotheses" code_rel_no_install;
