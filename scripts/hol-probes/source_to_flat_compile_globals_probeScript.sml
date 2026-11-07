(* Typed compiler global-effect theorems from the pinned source proof. *)
load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "op_theorem="; print_term (concl source_to_flatProofTheory.op_gbag_astOp_to_flatOp); print "\n");
val _ = (print "compile_theorem="; print_term (concl source_to_flatProofTheory.compile_exp_esgc_free); print "\n");
val _ = (print "make_varls_theorem="; print_term (concl source_to_flatProofTheory.make_varls_esgc_free); print "\n");
val _ = (print "compile_decs_theorem="; print_term (concl source_to_flatProofTheory.compile_decs_esgc_free); print "\n");
val _ = (print "compile_prog_theorem="; print_term (concl source_to_flatProofTheory.compile_prog_esgc_free); print "\n");
val _ = (print "inc_compile_prog_theorem="; print_term (concl source_to_flatProofTheory.inc_compile_prog_esgc_free); print "\n");
val _ = (print "compile_flat_esgc="; print_term (concl source_to_flatProofTheory.compile_flat_esgc_free); print "\n");
val _ = (print "compile_full_esgc="; print_term (concl source_to_flatProofTheory.compile_esgc_free); print "\n");
val _ = (print "inc_compile_full_esgc="; print_term (concl source_to_flatProofTheory.inc_compile_esgc_free); print "\n");
val _ = (print "compile_no_mat="; print_term (concl source_to_flatProofTheory.compile_no_Mat); print "\n");
val _ = (print "inc_compile_no_mat="; print_term (concl source_to_flatProofTheory.inc_compile_no_Mat); print "\n");
val _ = (print "num_bindings="; print_term (concl source_to_flatProofTheory.num_bindings_def); print "\n");
val _ = (print "compile_decs_num_bindings="; print_term (concl source_to_flatProofTheory.compile_decs_num_bindings); print "\n");
val _ = (print "set_globals_make_varls="; print_term (concl source_to_flatProofTheory.set_globals_make_varls); print "\n");
val _ = (print "compile_decs_elist_globals="; print_term (concl source_to_flatProofTheory.compile_decs_elist_globals); print "\n");
val _ = (print "compile_flat_sub_bag="; print_term (concl source_to_flatProofTheory.compile_flat_sub_bag); print "\n");
val _ = (print "compile_globals_distinct="; print_term (concl source_to_flatProofTheory.compile_globals_BAG_ALL_DISTINCT); print "\n");
val _ = (print "inc_compile_globals_distinct="; print_term (concl source_to_flatProofTheory.inc_compile_globals_BAG_ALL_DISTINCT); print "\n");
val _ = (print "monotonic_globals_oracle="; print_term (concl source_to_flatProofTheory.monotonic_globals_state_co_compile); print "\n");
val _ = (print "bag_inn="; print_term (concl bagTheory.BAG_INN); print "\n");
val _ = (print "sub_bag="; print_term (concl bagTheory.SUB_BAG); print "\n");
val _ = (print "bag_in="; print_term (concl bagTheory.BAG_IN); print "\n");
val _ = (print "sub_bag_imp="; print_term (concl source_to_flatProofTheory.SUB_BAG_IMP); print "\n");
val _ = (print "bag_all_distinct="; print_term (concl bagTheory.BAG_ALL_DISTINCT); print "\n");
val _ = (print "bag_all_distinct_sub_bag="; print_term (concl bagTheory.BAG_ALL_DISTINCT_SUB_BAG); print "\n");
val compile_flat_bag_all_distinct_local =
  MATCH_MP (bagTheory.BAG_ALL_DISTINCT_SUB_BAG |> REWRITE_RULE [GSYM AND_IMP_INTRO])
           source_to_flatProofTheory.compile_flat_sub_bag;
val _ = if null (hyp compile_flat_bag_all_distinct_local) then () else raise Fail "local theorem has hypotheses";
val _ = (print "compile_flat_bag_all_distinct_local="; print_term (concl compile_flat_bag_all_distinct_local); print "\n");
val _ = (print "mapi_snoc="; print_term (concl source_to_flatProofTheory.MAPi_SNOC); print "\n");
val _ = (print "list_size_definition="; print_term (concl listTheory.list_size_def); print "\n");
val _ = (print "list_size_theorem="; print_term (concl listTheory.list_size_thm); print "\n");
val mem_size_lemma_local = Q.prove (
  `list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)`,
  Induct_on `xs` >> rw [listTheory.list_size_def] >> fs []);
val _ = if null (hyp mem_size_lemma_local) then () else raise Fail "local theorem has hypotheses";
val _ = (print "mem_size_lemma_local="; print_term (concl mem_size_lemma_local); print "\n");
val _ = (print "ns_all_append="; print_term (concl namespacePropsTheory.nsAll_nsAppend); print "\n");
val _ = (print "ns_all_extend_env="; print_term (concl source_to_flatProofTheory.nsAll_extend_env); print "\n");
val snd_eq_local = Q.prove (`SND x = y ⇔ ∃a. x = (a,y)`, Cases_on `x` >> rw []);
val _ = if null (hyp snd_eq_local) then () else raise Fail "local theorem has hypotheses";
val _ = (print "snd_eq_local="; print_term (concl snd_eq_local); print "\n");
