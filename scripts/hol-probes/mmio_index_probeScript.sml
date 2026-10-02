load "preamble"; load "targetSemTheory";
open HolKernel Parse bossLib preamble targetSemTheory optionTheory;
val _ = Globals.linewidth := 100000;
val _ = print("mmio_full_def=" ^ term_to_string(concl mmio_pcs_min_index_def) ^ "\n");
val _ = print("mmio_type=" ^ type_to_string(type_of ``mmio_pcs_min_index``) ^ "\n");
val sh = prove (``(!j:num. x <= j /\ j < n ==> P j) <=> (!j. j < n ==> x <= j ==> P j)``, metis_tac []);
val bound = DECIDE ``!x:num. x <= 0 <=> x = 0``;
val pred = prove (``!x:num. (x <= LENGTH [] /\ (!j. j < x ==> ?s. EL j [] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [] ==> ?op. EL j [] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_empty=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val bound = DECIDE ``!x:num. x <= 1 <=> x = 0 \/ x = 1``;
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»] /\ (!j. j < x ==> ?s. EL j [ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»] ==> ?op. EL j [ExtCall «»] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_0=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_1=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_2=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val bound = DECIDE ``!x:num. x <= 2 <=> x = 0 \/ x = 1 \/ x = 2``;
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; ExtCall «»] ==> ?op. EL j [ExtCall «»; ExtCall «»] = SharedMem op)) <=> x = 2``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; ExtCall «»] = SOME 2``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_00=SOME 2\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedRead] ==> ?op. EL j [ExtCall «»; SharedMem MappedRead] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedRead] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_01=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedWrite] ==> ?op. EL j [ExtCall «»; SharedMem MappedWrite] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedWrite] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_02=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; ExtCall «»] ==> ?op. EL j [SharedMem MappedRead; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_10=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_11=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_12=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; ExtCall «»] ==> ?op. EL j [SharedMem MappedWrite; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_20=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_21=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_22=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val bound = DECIDE ``!x:num. x <= 3 <=> x = 0 \/ x = 1 \/ x = 2 \/ x = 3``;
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; ExtCall «»; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; ExtCall «»; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; ExtCall «»; ExtCall «»] ==> ?op. EL j [ExtCall «»; ExtCall «»; ExtCall «»] = SharedMem op)) <=> x = 3``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; ExtCall «»; ExtCall «»] = SOME 3``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_000=SOME 3\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; ExtCall «»; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; ExtCall «»; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; ExtCall «»; SharedMem MappedRead] ==> ?op. EL j [ExtCall «»; ExtCall «»; SharedMem MappedRead] = SharedMem op)) <=> x = 2``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; ExtCall «»; SharedMem MappedRead] = SOME 2``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_001=SOME 2\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; ExtCall «»; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; ExtCall «»; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; ExtCall «»; SharedMem MappedWrite] ==> ?op. EL j [ExtCall «»; ExtCall «»; SharedMem MappedWrite] = SharedMem op)) <=> x = 2``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; ExtCall «»; SharedMem MappedWrite] = SOME 2``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_002=SOME 2\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedRead; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedRead; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedRead; ExtCall «»] ==> ?op. EL j [ExtCall «»; SharedMem MappedRead; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedRead; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_010=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedRead; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedRead; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedRead; SharedMem MappedRead] ==> ?op. EL j [ExtCall «»; SharedMem MappedRead; SharedMem MappedRead] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedRead; SharedMem MappedRead] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_011=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedRead; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedRead; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedRead; SharedMem MappedWrite] ==> ?op. EL j [ExtCall «»; SharedMem MappedRead; SharedMem MappedWrite] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedRead; SharedMem MappedWrite] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_012=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedWrite; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedWrite; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedWrite; ExtCall «»] ==> ?op. EL j [ExtCall «»; SharedMem MappedWrite; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedWrite; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_020=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedWrite; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedWrite; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedWrite; SharedMem MappedRead] ==> ?op. EL j [ExtCall «»; SharedMem MappedWrite; SharedMem MappedRead] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedWrite; SharedMem MappedRead] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_021=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [ExtCall «»; SharedMem MappedWrite; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [ExtCall «»; SharedMem MappedWrite; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [ExtCall «»; SharedMem MappedWrite; SharedMem MappedWrite] ==> ?op. EL j [ExtCall «»; SharedMem MappedWrite; SharedMem MappedWrite] = SharedMem op)) <=> x = 1``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [ExtCall «»; SharedMem MappedWrite; SharedMem MappedWrite] = SOME 1``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_022=SOME 1\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; ExtCall «»; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; ExtCall «»; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; ExtCall «»; ExtCall «»] ==> ?op. EL j [SharedMem MappedRead; ExtCall «»; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; ExtCall «»; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_100=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; ExtCall «»; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; ExtCall «»; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; ExtCall «»; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead; ExtCall «»; SharedMem MappedRead] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; ExtCall «»; SharedMem MappedRead] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_101=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; ExtCall «»; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; ExtCall «»; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; ExtCall «»; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedRead; ExtCall «»; SharedMem MappedWrite] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; ExtCall «»; SharedMem MappedWrite] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_102=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedRead; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedRead; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedRead; ExtCall «»] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedRead; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedRead; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_110=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_111=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedRead; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_112=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedWrite; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedWrite; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedWrite; ExtCall «»] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedWrite; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedWrite; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_120=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_121=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedRead; SharedMem MappedWrite; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_122=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; ExtCall «»; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; ExtCall «»; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; ExtCall «»; ExtCall «»] ==> ?op. EL j [SharedMem MappedWrite; ExtCall «»; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; ExtCall «»; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_200=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; ExtCall «»; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; ExtCall «»; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; ExtCall «»; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedWrite; ExtCall «»; SharedMem MappedRead] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; ExtCall «»; SharedMem MappedRead] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_201=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; ExtCall «»; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; ExtCall «»; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; ExtCall «»; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedWrite; ExtCall «»; SharedMem MappedWrite] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; ExtCall «»; SharedMem MappedWrite] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_202=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedRead; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedRead; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedRead; ExtCall «»] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedRead; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedRead; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_210=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_211=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedRead; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_212=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; ExtCall «»] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedWrite; ExtCall «»] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; ExtCall «»] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedWrite; ExtCall «»] = SharedMem op)) <=> F``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedWrite; ExtCall «»] = NONE``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_220=NONE\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedRead] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedRead] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedRead] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedRead] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedRead] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_221=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val pred = prove (``!x:num. (x <= LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedWrite] /\ (!j. j < x ==> ?s. EL j [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedWrite] = ExtCall s) /\ (!j. x <= j /\ j < LENGTH [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedWrite] ==> ?op. EL j [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedWrite] = SharedMem op)) <=> x = 0``,
 gen_tac >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss() ++ CONJ_ss) [bound, RIGHT_AND_OVER_OR, sh])) >>
 CONV_TAC (LAND_CONV (REDEPTH_CONV (numLib.BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) [listTheory.EL])))) >> simp []);
val th = prove (``mmio_pcs_min_index [SharedMem MappedWrite; SharedMem MappedWrite; SharedMem MappedWrite] = SOME 0``, simp [mmio_pcs_min_index_def, pred]);
val _ = if null (hyp th) then print "mmio_222=SOME 0\n" else raise Fail "MMIO fixture has assumptions";
val _ = OS.Process.exit OS.Process.success;
