load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory wordConvsTheory;
val _ = Globals.linewidth := 1000000;
fun check name th original =
  if null(hyp th) andalso null(free_vars(concl th)) andalso aconv (concl th) (concl(GEN_ALL original))
  then () else raise Fail ("replay " ^ name);
val _ = (print "no_alloc_code_def="; print_term(concl no_alloc_code_def); print "\n");
val _ = (print "no_install_code_def="; print_term(concl no_install_code_def); print "\n");
val no_alloc_find_code_replay = GEN_ALL(prove(concl no_alloc_find_code,
  rw[no_alloc_code_def] >> Cases_on `dest` >>
  fs[find_code_def] >>
  EVERY_CASE_TAC >> fs [] >> rveq >>
  metis_tac[]));
val _ = check "no_alloc_find_code" no_alloc_find_code_replay no_alloc_find_code;
val _ = (print "no_alloc_find_code_statement="; print_term(concl no_alloc_find_code_replay); print "\n");
val _ = print("no_alloc_find_code_hypotheses=" ^ Int.toString(length(hyp no_alloc_find_code_replay)) ^ "\n");
val no_install_find_code_replay = GEN_ALL(prove(concl no_install_find_code,
  rw[no_install_code_def] >> Cases_on `dest` >> fs[find_code_def] >>
  EVERY_CASE_TAC >> fs [] >> rveq >>
  metis_tac[]));
val _ = check "no_install_find_code" no_install_find_code_replay no_install_find_code;
val _ = (print "no_install_find_code_statement="; print_term(concl no_install_find_code_replay); print "\n");
val _ = print("no_install_find_code_hypotheses=" ^ Int.toString(length(hyp no_install_find_code_replay)) ^ "\n");
val no_install_evaluate_const_code_replay = GEN_ALL(prove(concl no_install_evaluate_const_code,
  recInduct evaluate_ind >> rw[] >> qpat_x_assum `evaluate _ = _` mp_tac
  >~[`MustTerminate`]
  >-(gvs[evaluate_def,AllCaseEqs()]
     >> rpt strip_tac >> gvs[no_install_def] >>
     pairarg_tac >> fs[] >> every_case_tac >> gvs[])
  >~[`Seq`]
  >- (gvs[evaluate_def,AllCaseEqs()]
     >> rpt strip_tac >> gvs[no_install_def] >>
     pairarg_tac >> fs[] >> every_case_tac >> gvs[])
  >~[`Loop`]
  >- (
    gvs[evaluate_def,no_install_def] >>
    every_case_tac >> gvs[UNCURRY_EQ]>>
    rw[]>>gvs[AllCaseEqs()]>>
    imp_res_tac cut_state_const>>
    gvs[STOP_def,no_install_def]
  )
  >~[`Call`]
  >-(
  gvs[evaluate_def,AllCaseEqs()]
  >> rpt strip_tac >> gvs[no_install_def]
  >> imp_res_tac no_install_find_code >> fs[]
  >> imp_res_tac pop_env_const >>  gvs[])
  >> gvs[evaluate_def,AllCaseEqs()]
  >> rpt strip_tac >> gvs[no_install_def]
  >- (drule alloc_const >> fs[])
  >- (drule inst_const_full >> fs[])
  >- (drule mem_store_const >> fs[])
  >- (drule jump_exc_const >> fs[])
  >- (drule share_inst_const >> fs[])));
val _ = check "no_install_evaluate_const_code" no_install_evaluate_const_code_replay no_install_evaluate_const_code;
val _ = (print "no_install_evaluate_const_code_statement="; print_term(concl no_install_evaluate_const_code_replay); print "\n");
val _ = print("no_install_evaluate_const_code_hypotheses=" ^ Int.toString(length(hyp no_install_evaluate_const_code_replay)) ^ "\n");
