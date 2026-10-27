load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm =
  let val result = rhs (concl (EVAL tm))
      val simplified = rhs (concl ((SIMP_CONV (srw_ss()) [] result) handle Conv.UNCHANGED => REFL result))
  in print label; print_term simplified; print "\n" end;
fun show_true label tm =
  let val th = prove(tm, simp [flatSemTheory.check_type_def])
  in if null (hyp th) then (print label; print "T\n") else raise Fail label end;
val _ = show_thm "check_type_typed=" flatSemTheory.check_type_def;
val _ = show_thm "dest_litv_typed=" flatSemTheory.dest_Litv_def;
val _ = show_thm "v_to_flat_typed=" flatSemTheory.v_to_flat_def;
val _ = show_thm "flat_to_v_typed=" flatSemTheory.flat_to_v_def;
val _ = show_thm "v_rel_check_type_typed=" source_to_flatProofTheory.v_rel_check_type;
val _ = show_thm "check_type_to_flat_typed=" source_to_flatProofTheory.check_type_IMP_v_rel;
val _ = show_thm "check_type_from_flat_typed=" source_to_flatProofTheory.check_type_v_rel_flat_to_v;
val _ = show_thm "check_type_from_flat_list_typed=" source_to_flatProofTheory.check_type_v_rel_MAP_flat_to_v;
val _ = show_thm "bind_exn_typed=" flatSemTheory.bind_exn_v_def;
val _ = show_thm "chr_exn_typed=" flatSemTheory.chr_exn_v_def;
val _ = show_thm "div_exn_typed=" flatSemTheory.div_exn_v_def;
val _ = show_thm "subscript_exn_typed=" flatSemTheory.subscript_exn_v_def;
val _ = show_thm "do_if_typed=" flatSemTheory.do_if_def;
val _ = show_thm "do_if_either_or_typed=" flatSemTheory.do_if_either_or;
val _ = show_thm "boolean_relation_typed=" source_to_flatProofTheory.v_rel_Bool_eqn;
val local_eqns =
  [``source_to_flatProof$v_rel genv (Litv l) v``, ``source_to_flatProof$v_rel genv (Conv cn vs) v``,
   ``source_to_flatProof$v_rel genv (Loc b l) v``, ``source_to_flatProof$v_rel genv (Vectorv vs) v``,
   ``source_to_flatProof$env_rel genv nsEmpty env'``, ``source_to_flatProof$env_rel genv (nsBind x v env) env'``,
   ``source_to_flatProof$v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once source_to_flatProofTheory.v_rel_cases])
  |> map GEN_ALL |> LIST_CONJ;
val values_rel = prove(
  ``!genv. source_to_flatProof$genv_c_ok genv.c ⇒
    (!b. source_to_flatProof$v_rel genv (semanticPrimitives$Boolv b) (flatSem$Boolv b)) ∧
    source_to_flatProof$v_rel genv semanticPrimitives$div_exn_v flatSem$div_exn_v ∧
    source_to_flatProof$v_rel genv semanticPrimitives$chr_exn_v flatSem$chr_exn_v ∧
    source_to_flatProof$v_rel genv semanticPrimitives$bind_exn_v flatSem$bind_exn_v ∧
    source_to_flatProof$v_rel genv semanticPrimitives$sub_exn_v flatSem$subscript_exn_v``,
  rw [semanticPrimitivesTheory.div_exn_v_def, flatSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, flatSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, flatSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, flatSemTheory.subscript_exn_v_def,
      local_eqns, source_to_flatProofTheory.genv_c_ok_def,
      source_to_flatProofTheory.has_exns_def, source_to_flatProofTheory.has_bools_def,
      semanticPrimitivesTheory.Boolv_def, flatSemTheory.Boolv_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp [local_eqns]);
val _ = show_thm "values_rel_typed=" values_rel;
val _ = show_eval "true_bool=" ``flatSem$check_type BoolT (flatSem$Boolv T)``;
val _ = show_eval "false_bool=" ``flatSem$check_type BoolT (flatSem$Boolv F)``;
val _ = show_eval "wrong_bool=" ``flatSem$check_type BoolT (flatSem$Conv (SOME (2, SOME 0)) [])``;
val _ = show_true "int_type=" ``flatSem$check_type IntT (flatSem$Litv (IntLit 7))``;
val _ = show_eval "wrong_int=" ``flatSem$check_type IntT (flatSem$Litv (Char #"a"))``;
val _ = show_true "word8_type=" ``flatSem$check_type (WordT W8) (flatSem$Litv (Word8 7w))``;
val _ = show_true "word64_type=" ``flatSem$check_type (WordT W64) (flatSem$Litv (Word64 7w))``;
val _ = show_eval "literal_projection=" ``flatSem$dest_Litv (flatSem$Litv (IntLit 7))``;
val _ = show_eval "nonliteral_projection=" ``flatSem$dest_Litv (flatSem$Conv NONE [])``;
val _ = show_eval "to_flat_true=" ``flatSem$v_to_flat (semanticPrimitives$Boolv T)``;
val _ = show_eval "to_flat_other=" ``flatSem$v_to_flat (semanticPrimitives$Loc T 4)``;
val _ = show_eval "from_flat_false=" ``flatSem$flat_to_v (flatSem$Boolv F)``;
val _ = show_eval "from_flat_other=" ``flatSem$flat_to_v (flatSem$Loc T 4)``;
val _ = show_eval "if_true=" ``flatSem$do_if (flatSem$Boolv T) (3 :num) 4``;
val _ = show_eval "if_false=" ``flatSem$do_if (flatSem$Boolv F) (3 :num) 4``;
val _ = show_eval "if_non_bool=" ``flatSem$do_if (flatSem$Litv (IntLit 1)) (3 :num) 4``;
