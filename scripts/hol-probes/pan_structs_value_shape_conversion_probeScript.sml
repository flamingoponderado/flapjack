load "preamble";
load "pan_structsProofTheory";
open HolKernel Parse bossLib preamble pan_structsProofTheory pan_structsTheory panSemTheory panPropsTheory panLangTheory pan_commonPropsTheory listTheory alistTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL shape_of_convert_v;
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = print "shape_of_convert_v_statement=";
val _ = print_term(concl original);
val _ = print "\n";
val _ = print("shape_of_convert_v_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl original)))) ^ "\n");
val _ = print("shape_of_convert_v_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
val _ = print("shape_of_convert_v_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");

val wf_shape_struct_infos_ok_helper = Q.prove (`  ALOOKUP (DROP n ctxt) nm = SOME info /\
  struct_infos_ok ctxt ==>
  ?i.
  afindi nm (DROP n ctxt) = SOME i /\
  i + n < LENGTH ctxt /\
  EL (i + n) ctxt = (nm, info) /\
  afindi nm ctxt = SOME (i + n) /\
  (!sh. MEM sh (MAP SND info.fields) ==> is_wf_shape (DROP (i + n + 1) ctxt) sh)`,
  rw [struct_infos_ok_def]
  >> subgoal `?c1 c2. ctxt = c1 ++ c2 /\ LENGTH c1 = n`
  >- (
    map_every qexists_tac [`TAKE n ctxt`, `DROP n ctxt`]
    >> simp []
    >> Cases_on `n < LENGTH ctxt`
    >> fs [DROP_LENGTH_TOO_LONG]
  )
  >> fs [DROP_APPEND2]
  >> qspecl_then [`nm`, `c1`, `c2`] mp_tac afindi_append
  >> simp []
  >> Cases_on `ALOOKUP c1 nm`
  >- (
    fs [ALOOKUP_eq_afindi, EL_APPEND2]
    >> imp_res_tac afindi_less_length
    >> imp_res_tac afindi_EL
    >> fs []
    >> simp [PAIR_FST_SND_EQ]
    >> rw []
    >> first_x_assum (qspec_then `i + LENGTH c1` mp_tac)
    >> simp [EL_APPEND2, PAIR_FST_SND_EQ, EVERY_MEM, DROP_APPEND2]
  )
  >- (
    imp_res_tac ALOOKUP_MEM
    >> fs [ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    >> metis_tac []
  ));

val shape_of_convert_v_ind = Q.prove (`  ! str_ctxt n sh v.
  struct_infos_ok ctxt /\
  is_wf_shape (DROP n ctxt) sh /\
  v_flds_ok ctxt v /\
  str_ctxt = MAP (λ(nm,info). (nm, info.fields)) ctxt /\
  shape_of v = sh ==>
  compile_shape_n str_ctxt n sh = shape_of (convert_v v)`,
  recInduct compile_shape_n_ind
  >> simp [convert_v_def, shape_of_def, compile_shape_n_def,
        compile_shapes_eq_map, MAP_MAP_o, shape_of_val, v_flds_ok_def,
        shape_of_def]
  >> rw []
  >> Cases_on `v`
  >> fs [shape_of_def, shape_of_val, convert_v_def, v_flds_ok_def]
  >- (
    gvs [MAP_MAP_o, o_DEF, MEM_MAP, PULL_EXISTS, is_wf_shape_def, EVERY_MAP]
    >> irule MAP_CONG
    >> fs [v_flds_ok_def, EVERY_MEM]
  )
  >- (
    fs [is_wf_shape_def, CasePred "option"]
    >> drule_then drule wf_shape_struct_infos_ok_helper
    >> strip_tac
    >> fs [GSYM MAP_DROP, afindi_MAP_eq, EL_MAP, GSYM MAP_MAP_o]
    >> gs [LIST_EQ_REWRITE, EL_MAP, ALOOKUP_eq_afindi]
    >> rw []
    >> irule EQ_TRANS
    >> first_x_assum (irule_at Any)
    >> first_x_assum (irule_at Any)
    >> simp [ELIM_UNCURRY, EL_MEM, EL_MAP]
    >> simp [MEM_MAP]
    >> drule_then (irule_at Any) EL_MEM
    >> fs [EVERY_EL, ELIM_UNCURRY]
  ));
val original_ind = GEN_ALL shape_of_convert_v_ind;
val _ = if null(hyp original_ind) andalso null(free_vars(concl original_ind)) then () else raise Fail "open induction theorem";
val _ = print "shape_of_convert_v_ind_statement=";
val _ = print_term(concl original_ind);
val _ = print "\n";
val _ = print("shape_of_convert_v_ind_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl original_ind)))) ^ "\n");
val _ = print("shape_of_convert_v_ind_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original_ind))) ^ "\n");
val reversed = GEN_ALL (SIMP_RULE std_ss [] (GSYM shape_of_convert_v));
val _ = print "shape_of_convert_v_rev_statement=";
val _ = print_term(concl reversed);
val _ = print "\n";
val _ = print("shape_of_convert_v_rev_types=" ^ String.concatWith ";" (map (fn t => term_to_string t ^ ":" ^ type_to_string(type_of t)) (fst(strip_forall(concl reversed)))) ^ "\n");
val _ = print("shape_of_convert_v_rev_proved=" ^ term_to_string(rhs(concl(EQT_INTRO reversed))) ^ "\n");
