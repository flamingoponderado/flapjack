load "preamble";
load "helperLib";
open helperLib;
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory stackLangTheory;
val _ = Globals.linewidth := 20000;
val single_run_events = prove(``   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events``,
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const] >>
  fs[] >> rpt (drule_then MATCH_MP_TAC IS_PREFIX_TRANS) >> fs[]
  >~[`sh_mem_op`]
  >-(
    gvs[oneline sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
    sh_mem_load32_def,sh_mem_store32_def,sh_mem_load_byte_def,
    sh_mem_load16_def,sh_mem_store16_def,
    sh_mem_store_byte_def,ffiTheory.call_FFI_def,AllCaseEqs()])
  >-(gvs[ffiTheory.call_FFI_def,AllCaseEqs()]));
val _ = if null(hyp single_run_events) andalso null(free_vars(concl single_run_events)) then () else raise Fail "open theorem";
val _ = print("single_run_events_statement=" ^ term_to_string(concl single_run_events) ^ "\n");
val _ = print("single_run_events_proved=" ^ term_to_string(rhs(concl(EQT_INTRO single_run_events))) ^ "\n");
