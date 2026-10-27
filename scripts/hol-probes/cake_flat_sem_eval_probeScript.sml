load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "dec_clock_typed=" flatSemTheory.dec_clock_def;
val _ = show_thm "fix_clock_typed=" flatSemTheory.fix_clock_def;
val _ = show_thm "bytes_typed=" flatSemTheory.v_to_bytes_def;
val _ = show_thm "words_typed=" flatSemTheory.v_to_words_def;
val _ = show_thm "do_eval_typed=" flatSemTheory.do_eval_def;
val _ = show_thm "app_unit_typed=" flatSemTheory.AppUnit_def;
val fix_clock_imp = prove(
  ``flatSem$fix_clock s x = (s1,res) ⇒ s1.clock ≤ s.clock``,
  Cases_on `x` >> fs [flatSemTheory.fix_clock_def] >> rw [] >> fs []);
val _ = show_thm "fix_clock_imp_typed=" fix_clock_imp;
val _ = show_eval "zero_clock=" ``(flatSem$dec_clock ((ARB : (unit,unit) flatSem$state) with clock := 0)).clock``;
val _ = show_eval "decrement=" ``(flatSem$dec_clock ((ARB : (unit,unit) flatSem$state) with clock := 4)).clock``;
val _ = show_eval "fix_clamps=" ``(FST (flatSem$fix_clock ((ARB : (unit,unit) flatSem$state) with clock := 3)
  (((ARB : (unit,unit) flatSem$state) with clock := 7), T))).clock``;
val _ = show_eval "empty_eval=" ``flatSem$do_eval [] (ARB : unit flatSem$install_config)``;
val bytes_valid = prove(
  ``flatSem$v_to_bytes (flatSem$list_to_v [Litv (Word8 2w); Litv (Word8 255w)]) = SOME [2w; 255w]``,
  simp [flatSemTheory.v_to_bytes_def, flatSemTheory.list_to_v_def, flatSemTheory.v_to_list_def,
        backend_commonTheory.nil_tag_def, backend_commonTheory.cons_tag_def, flatSemTheory.list_id_def] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp [listTheory.MAP_EQ_CONS] >> metis_tac []);
val _ = if null (hyp bytes_valid) then print "bytes_valid=SOME [2w; 255w]\n" else raise Fail "bytes_valid";
val words_valid = prove(
  ``flatSem$v_to_words (flatSem$list_to_v [Litv (Word64 4w)]) = SOME [4w]``,
  simp [flatSemTheory.v_to_words_def, flatSemTheory.list_to_v_def, flatSemTheory.v_to_list_def,
        backend_commonTheory.nil_tag_def, backend_commonTheory.cons_tag_def, flatSemTheory.list_id_def] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp [listTheory.MAP_EQ_CONS] >> metis_tac []);
val _ = if null (hyp words_valid) then print "words_valid=SOME [4w]\n" else raise Fail "words_valid";
val eval_success = prove(
  ``OPTION_MAP (λ(decs, config, v). (LENGTH decs, FST (config.compile_oracle 0)))
      (flatSem$do_eval [flatSem$list_to_v [Litv (Word8 2w); Litv (Word8 255w)];
                        flatSem$list_to_v [Litv (Word64 4w)]]
        (<| compile := (λst ds. SOME ([2w; 255w], [4w], 2));
            compile_oracle := (λn. if n = 0 then (1, [flatLang$Lit backend_common$None (IntLit 1)]) else (2, [])) |>
          : num flatSem$install_config)) = SOME (1, 2)``,
  simp [flatSemTheory.do_eval_def, bytes_valid, words_valid, miscTheory.shift_seq_def]);
val _ = if null (hyp eval_success) then print "eval_success=SOME (1,2)\n" else raise Fail "eval_success";
