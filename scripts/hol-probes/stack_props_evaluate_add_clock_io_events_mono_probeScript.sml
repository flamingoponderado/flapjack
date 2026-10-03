load "preamble";
load "helperLib";
open helperLib;
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory stackLangTheory;
val _ = Globals.linewidth := 20000;
(* The original [local,simp] helper is not exported by stackPropsTheory. *)
val sh_mem_op_with_const = prove(``
   (sh_mem_op op x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_op op x y z)``,
  gs[oneline sh_mem_op_def] >>
  TOP_CASE_TAC >> gs[]);
val _ = augment_srw_ss [rewrites [sh_mem_op_with_const]];
val extra_clock_events = GEN_ALL(prove(``
   ∀e s.
     (SND(evaluate(e,s))).ffi.io_events ≼
     (SND(evaluate(e,s with clock := s.clock + extra))).ffi.io_events``,
  rw[oneline SND] >> ntac 2 (TOP_CASE_TAC >> fs[]) >>
  reverse $ Cases_on `q = (SOME TimeOut)` >> gvs[]
  >- (
     drule_all evaluate_add_clock >>
     strip_tac >> gvs[]) >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac (rev [`e`,`s`,`r`,`q'`,`r'`]) >>
  recInduct evaluate_ind >> rpt conj_tac
  >~ [`Seq`]
  >-
    (rpt strip_tac >> pop_assum mp_tac >>
    gvs[evaluate_def,UNCURRY_EQ,AllCaseEqs()]
    >-(imp_res_tac evaluate_add_clock >> fs[]) >>
    strip_tac >> gvs[] >>
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    METIS_TAC[IS_PREFIX_TRANS])
  >~ [`Loop`]
  >-
    (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7] >>
    imp_res_tac evaluate_add_clock >> fs[] >>
    Cases_on ‘res = SOME TimeOut’ >> gvs [] >>
    gvs[AllCaseEqs()] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    Cases_on ‘res' = SOME TimeOut’ >> gvs [] >>
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    METIS_TAC[IS_PREFIX_TRANS])
  >~ [`JumpLower`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7]
    >-(
      gvs[AllCaseEqs(),UNCURRY_EQ] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      METIS_TAC[IS_PREFIX_TRANS]) >>
    gvs[AllCaseEqs()]
    >- (fsrw_tac[ARITH_ss][dec_clock_def])
    >- (fsrw_tac[ARITH_ss][dec_clock_def]))
  >~ [`RawCall`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7]
    >-(
      gvs[AllCaseEqs(),UNCURRY_EQ] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      METIS_TAC[IS_PREFIX_TRANS]) >>
    gvs[AllCaseEqs()]
    >- fsrw_tac[ARITH_ss][dec_clock_def]
    >- fsrw_tac[ARITH_ss][dec_clock_def])
  >~ [`Call`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 2]
    >- (
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 2]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
      gvs[AllCaseEqs()] >>
      fsrw_tac[ARITH_ss][dec_clock_def])
    >- (
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 5]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 3]
      >-(
        imp_res_tac evaluate_add_clock >> fs[] >>
        fsrw_tac[ARITH_ss][dec_clock_def] >>
        gvs[] >> gvs[AllCaseEqs()])
      >-(
        imp_res_tac evaluate_add_clock >> fs[] >>
        fsrw_tac[ARITH_ss][dec_clock_def] >>
        gvs[] >> gvs[AllCaseEqs()]) >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 3]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS])
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS])))
  >~ [`ShMemOp`]
  >- (rpt strip_tac >>
     imp_res_tac evaluate_io_events_mono >>
     gvs[evaluate_def,AllCaseEqs()] >>
     fsrw_tac[ARITH_ss][dec_clock_def] >>
     gvs[pair_map_eq])
  >> (rpt (strip_tac) >> gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ] >>
  NO_TAC)));
val _ = if null(hyp extra_clock_events) andalso null(free_vars(concl extra_clock_events)) then () else raise Fail "open theorem";
val _ = print("extra_clock_events_statement=" ^ term_to_string(concl extra_clock_events) ^ "\n");
val _ = print("extra_clock_events_proved=" ^ term_to_string(rhs(concl(EQT_INTRO extra_clock_events))) ^ "\n");
