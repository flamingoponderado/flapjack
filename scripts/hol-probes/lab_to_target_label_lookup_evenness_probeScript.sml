load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val lab_lookup_IMP=Q.prove(`  (lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)`,
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);
;
val case_eq_thms0 = map TypeBase.case_eq_of [``:lab``, ``:'a option``]
val bool_case_eq_thms = map (fn th =>
  let val v = th |> concl |> lhs |> rhs
  in th |> GEN v |> Q.ISPEC`T` |> SIMP_RULE bool_ss [] end) case_eq_thms0;
val all_enc_ok_split = Q.prove(
`  ∀c labs ffis pos k lines xs.
  all_enc_ok c labs ffis pos (Section k lines::xs) ⇒
  all_enc_ok c labs ffis pos [Section k lines] ∧
  all_enc_ok c labs ffis (pos + sec_length lines 0) xs`,
  Induct_on`lines`>>rw[all_enc_ok_def,sec_length_def,all_enc_ok_def]>>
  Cases_on`h`>>TRY(Cases_on`a`)>>
  fs[sec_length_def,sec_length_add,line_length_def,line_ok_def]>>rveq>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[] >>
  rfs[]>>
  metis_tac[ADD_ASSOC]);
val _=if null(hyp all_enc_ok_split) then () else raise Fail "open original replay hypotheses";
val all_enc_ok_even = Q.prove(
`  ∀lines pos.
  all_enc_ok c labs ffis pos [Section k lines] ⇒
  EVEN (sec_length lines pos)`,
  Induct>>fs[all_enc_ok_def,sec_length_def]>>Cases>>
  TRY(Cases_on`a`)>>
  rw[]>>fs[line_ok_def,line_length_def,sec_length_add,sec_length_def]>>
  rfs[]>>
  `n + sec_length lines pos = sec_length lines (n + pos)` by
    metis_tac[sec_length_add,ADD_COMM]>>
  fs[]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]);
val _=if null(hyp all_enc_ok_even) then () else raise Fail "open original replay hypotheses";
val all_enc_ok_lab_lookup_even = Q.prove(
`  ∀c labs ffis pos sec_list l1 l2 acc x.
      all_enc_ok c labs ffis pos sec_list ∧
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME x ∧
      (∀x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) ∧
      EVEN pos ⇒
      EVEN x`,
  Induct_on`sec_list`>>
  fs[all_enc_ok_def,compute_labels_alt_def]>>
  Cases \\ fs[compute_labels_alt_def] \\
  rw[] \\
  imp_res_tac all_enc_ok_split
  \\ pairarg_tac \\ fs[]
  \\ last_x_assum(match_mp_tac o MP_CANON)
  \\ fs[]
  \\ asm_exists_tac \\ fs[]
  \\ imp_res_tac all_enc_ok_even
  \\ qspecl_then[`pos`,`l`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`l`,`0`,`pos`]mp_tac sec_length_add \\ rw[] \\ fs[]
  \\ asm_exists_tac \\ fs[EVEN_ADD]
  \\ rw[lab_lookup_def,lookup_insert]
  \\ fs[lookup_fromAList]
  \\ pop_assum mp_tac \\ rw[] \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ match_mp_tac lines_ok_section_lab_lookup_even
  \\ asm_exists_tac \\ fs[]
  \\ qexists_tac`[]` \\ simp[]);
val _=if null(hyp all_enc_ok_lab_lookup_even) then () else raise Fail "open original replay hypotheses";
val _=capture "lines_ok_section_lab_lookup_even" lines_ok_section_lab_lookup_even;
val _=types "lines_ok_section_lab_lookup_even_types" lines_ok_section_lab_lookup_even;
val _=capture "all_enc_ok_split" all_enc_ok_split;
val _=types "all_enc_ok_split_types" all_enc_ok_split;
val _=capture "all_enc_ok_even" all_enc_ok_even;
val _=types "all_enc_ok_even_types" all_enc_ok_even;
val _=capture "all_enc_ok_lab_lookup_even" all_enc_ok_lab_lookup_even;
val _=types "all_enc_ok_lab_lookup_even_types" all_enc_ok_lab_lookup_even;
val _=show_types:=false;
fun observe label q=(print(label ^ "=");print_term(rconc((EVAL THENC QCONV(SIMP_CONV(srw_ss())[sptreeTheory.lookup_insert,sptreeTheory.lookup_def])) q));print "\n");
val cfg = ``<| ISA := RISC_V; encode := (λa. case a of
 Inst Skip => [0w;0w] | Jump w => [w2w w;99w]
 | JumpCmp c r ri w => [w2w w;88w] | Loc r w => [w2w w;77w]
 | _ => [10w;11w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (128w,127w); hw_offset := (128w,127w); byte_offset := (128w,127w);
 jump_offset := (128w,127w); cjump_offset := (128w,127w); loc_offset := (128w,127w)
 |> : 8 asm_config``;
val labs = ``insert 1 (insert 5 20 LN) LN : num num_map num_map``;
val ffis = ``[ExtCall (implode "a"); ExtCall (implode "b")]``;
val lines=``[Label 7 2 0;Asm(Asmi(Inst Skip)) [0w;0w] 2;LabAsm(Jump(Lab 1 5)) 99w [14w;99w] 2;Label 7 2 0;Label 9 0 0]:8 labLang$line list``;
val aux=``[(0,22);(2,40);(2,3);(9,60)]:(num#num)list``;
val code=``[Section 7 ^lines;Section 8 []]:8 labLang$sec list``;
val initial=``sptree$insert 99 (sptree$fromAList [(5,2**80);(6,3)]) sptree$LN:num sptree$num_map sptree$num_map``;
val _=observe "mixed_full_section_tuple" ``section_labels 4 ^lines ^aux=(8,[(2,8);(2,4);(0,22);(2,40);(2,3);(9,60)])``;
val _=observe "full_lines_valid" ``lines_ok ^cfg ^labs ^ffis 4 ^lines``;
val _=observe "hidden_odd_accumulator_first_match" ``ALOOKUP ^aux 2=SOME 40 /\ ALOOKUP(SND(section_labels 4 ^lines ^aux)) 2=SOME 8``;
val _=observe "full_code_valid_even_end" ``all_enc_ok ^cfg ^labs ^ffis 4 ^code /\ sec_length ^lines 4=8``;
val _=observe "full_computed_nested_map" ``compute_labels_alt 4 ^code ^initial=sptree$insert 8 (sptree$fromAList [(0,8)]) (sptree$insert 7 (sptree$fromAList [(0,4);(2,8);(2,4)]) ^initial)``;
val _=observe "old_map_query_local_guard" ``lab_lookup 7 2 (compute_labels_alt 4 ^code ^initial)=SOME 8 /\ lab_lookup 99 5 (compute_labels_alt 4 ^code ^initial)=SOME(2**80) /\ lab_lookup 99 6 (compute_labels_alt 4 ^code ^initial)=SOME 3``;
val _=observe "duplicate_sections_no_distinct_guard" ``let code=[Section 7 ^lines;Section 7 [Label 99 4 0]]:8 labLang$sec list in all_enc_ok ^cfg ^labs ^ffis 4 code /\ lab_lookup 7 4 (compute_labels_alt 4 code ^initial)=SOME 8 /\ lab_lookup 7 2 (compute_labels_alt 4 code ^initial)=NONE``;
val _=observe "even_start_guard_needed" ``let c=(^cfg with encode:=K[0w]);code=[Section 7 [Asm(Asmi(Inst Skip)) [0w] 1]]:8 labLang$sec list in all_enc_ok c ^labs ^ffis 3 code /\ lab_lookup 7 0 (compute_labels_alt 3 code sptree$LN)=SOME 3``;
val _=observe "validity_guard_needed" ``let code=[Section 7 [Label 99 2 1]]:8 labLang$sec list in ~all_enc_ok ^cfg ^labs ^ffis 4 code /\ lab_lookup 7 2 (compute_labels_alt 4 code sptree$LN)=SOME 5``;
val _=observe "accumulator_parity_guard_needed" ``lines_ok ^cfg ^labs ^ffis 4 [] /\ ALOOKUP(SND(section_labels 4 ([]:8 labLang$line list) [(2,3)])) 2=SOME 3``;
val _=observe "width1_empty_retained" ``compute_labels_alt 17 ([]:1 labLang$sec list) ^initial=^initial``;
val _=observe "width80_large_position" ``lab_lookup 7 5 (compute_labels_alt (2**80) ([Section 7 [Label 99 5 0]]:80 labLang$sec list) ^initial)=SOME(2**80)``;
