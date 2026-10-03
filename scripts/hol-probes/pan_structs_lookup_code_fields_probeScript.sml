load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory panLangTheory panSemTheory;
val _ = Globals.linewidth := 1000000;
open panPropsTheory pan_commonPropsTheory pan_structsTheory;
val compile_exp_correct_mmap_helper = Q.prove (`  !es vs. OPT_MMAP (eval s) es = SOME vs /\
  (!e. MEM e es ==> (!v. eval s e = SOME v ==>
    eval (convert_s ctxt s) (compile_exp ctxt e) = SOME (convert_v v))) ==>
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt es) = SOME (MAP convert_v vs)`,
  Induct
  >> simp [compile_exp_def, DISJ_IMP_THM, FORALL_AND_THM]
  >> rw []
  >> simp []
);
val opt_mmap_eq_every = Q.prove (`  OPT_MMAP f xs = SOME ys /\
  (!x y. MEM x xs /\ f x = SOME y ==> P y) ==>
  EVERY P ys`,
  rw [EVERY_EL]
  >> imp_res_tac opt_mmap_length_eq >> fs []
  >> imp_res_tac opt_mmap_el >> fs []
  >> gs []
  >> res_tac
  >> metis_tac [EL_MEM]
);
val map_uncurry_zip_again = Q.prove (`  LENGTH xs = LENGTH ys ==>
  MAP (\(x, y). (f x, g y)) (ZIP (xs, ys)) = ZIP (MAP f xs, MAP g ys)`,
  simp [LIST_EQ_REWRITE, EL_MAP, EL_ZIP, FORALL_PROD]
);
val shape_of_convert_v_rev = SIMP_RULE std_ss [] (GSYM shape_of_convert_v);
val source_theorem = Q.prove (
`  OPT_MMAP (eval s) argexps = SOME args ∧
  lookup_code s.code fname args = SOME (prog, newlocals, rshape) ∧
  alist_to_fmap ctxt.locals = FMAP_MAP2 (shape_of o SND) s.locals ∧
  alist_to_fmap ctxt.globals = FMAP_MAP2 (shape_of o SND ) s.globals ∧
  ctxt.structs = MAP (\(nm, info). (nm, info.fields)) s.structs ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.locals ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) s.globals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.locals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) s.globals ∧
  struct_infos_ok s.structs ⇒
  OPT_MMAP (eval (convert_s ctxt s)) (compile_exps ctxt argexps) =
    SOME (MAP convert_v args) ∧
  EVERY (\v. v_flds_ok s.structs v) args ∧
  (? new_l.
  lookup_code (convert_s ctxt s).code fname (MAP convert_v args) =
    SOME (compile (ctxt with locals := new_l) prog,
        FMAP_MAP2 (λ(nm,v). convert_v v) newlocals, (compile_shape ctxt.structs rshape)) ∧
    alist_to_fmap new_l = FMAP_MAP2 (shape_of o SND) newlocals
  ) ∧
  FEVERY (\(nm, v). v_flds_ok s.structs v) newlocals ∧
  FEVERY (\(nm, v). is_wf_shape_v s.structs v) newlocals`,
  strip_tac
  >> subgoal `EVERY (\v. is_wf_shape_v s.structs v ∧ v_flds_ok s.structs v) args`
  >- (
    drule_then irule opt_mmap_eq_every
    >> rw []
    >> imp_res_tac eval_is_wf_shape_v
    >> drule_then drule compile_exp_correct
    >> simp []
  )
  >> subgoal `FEVERY (\(nm, v). MEM v args) newlocals`
  >- (
    gvs [lookup_code_def, option_case_eq, bool_case_eq, pair_case_eq]
    >> rw [FEVERY_ALL_FLOOKUP, alistTheory.flookup_fupdate_list, option_case_eq]
    >> dxrule ALOOKUP_MEM
    >> rw []
    >> dxrule_at Any MEM_ZIP_MEM_MAP
    >> fs [LIST_REL_EL_EQN]
  )
  >> rpt conj_tac
  >- (
    irule compile_exp_correct_mmap_helper
    >> simp [compile_exp_correct]
  )
  >- (
    fs [EVERY_MEM]
  )
  >- (
    gvs [lookup_code_def, convert_s_def, option_case_eq, bool_case_eq, pair_case_eq]
    >> fs [convert_code_def, FLOOKUP_FMAP_MAP2,
        FMAP_MAP2_FUPDATE_LIST, FMAP_MAP2_FEMPTY, LIST_REL_MAP]
    >> irule_at Any EQ_REFL
    >> fs [LIST_REL_EL_EQN, EVERY_EL]
    >> simp [map_uncurry_zip_again, fm_empty_zip_alist]
    >> drule_at (Pat `struct_infos_ok _`) shape_of_convert_v_rev
    >> rw []
    >> AP_TERM_TAC
    >> irule LIST_EQ
    >> simp [EL_MAP, EL_ZIP, PAIR_FST_SND_EQ]
  )
  >- (
    fs [FEVERY_ALL_FLOOKUP, EVERY_MEM]
    >> metis_tac []
  )
  >- (
    fs [FEVERY_ALL_FLOOKUP, EVERY_MEM]
    >> metis_tac []
  )
);
val theorem_full = GEN_ALL source_theorem;
val _ = if null(hyp theorem_full) andalso null(free_vars(concl theorem_full)) then () else raise Fail "open theorem";
val _ = print "lookup_code_flds_ok_statement=";
val _ = print_term(concl theorem_full);
val _ = print "\n";
val _ = print("lookup_code_flds_ok_proved=" ^ term_to_string(rhs(concl(EQT_INTRO theorem_full))) ^ "\n");
val _ = print("lookup_code_flds_ok_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl theorem_full)))) ^ "\n");
