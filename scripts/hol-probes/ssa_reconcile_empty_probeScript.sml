load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_reconcile_moves_eq = prove (``∀L.
    FILTER (λ(a,b). a ≠ b)
      (FLAT (MAP (λv. case lookup v m of
                      | NONE => []
                      | SOME cv => [(f v, cv)]) L)) =
    MAP (λv. (f v, THE (lookup v m)))
      (FILTER (λv. case lookup v m of NONE => F | SOME cv => f v ≠ cv) L)``,
  Induct >> simp[] >>
  strip_tac >>
  Cases_on `lookup h m` >> fs[] >>
  IF_CASES_TAC >> simp[]);
val ssa_reconcile_filtered_all_distinct = prove (``ALL_DISTINCT (FILTER (λv. case lookup v cur_ssa of
                            | NONE => F
                            | SOME cv => option_lookup tgt_ssa v ≠ cv)
                  (MAP FST (toAList ns)))``,
  match_mp_tac FILTER_ALL_DISTINCT >>
  simp[ALL_DISTINCT_MAP_FST_toAList]);
val ssa_reconcile_get_vars_lemma = prove (``∀ls cur_ssa (cst:('a,'b,'c) wordSem$state).
    ALL_DISTINCT ls ∧
    (∀v. MEM v ls ⇒
         ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val) ⇒
    ∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
         LENGTH vs = LENGTH ls ∧
         ∀i. i < LENGTH ls ⇒
             lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)``,
  Induct >- simp[get_vars_def] >>
  rpt strip_tac >>
  fs[] >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
        LENGTH vs = LENGTH ls ∧
        ∀i. i < LENGTH ls ⇒
            lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)`
    by (first_x_assum match_mp_tac >> rpt strip_tac >>
        last_x_assum match_mp_tac >> simp[]) >>
  `∃val. lookup (THE (lookup h cur_ssa)) cst.locals = SOME val`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  qexists_tac `val::vs` >>
  simp[get_vars_def, get_var_def] >>
  Cases >> simp[]);
val alookup_zip_map_some = prove (``∀ls vs i f.
    ALL_DISTINCT (MAP f ls) ∧
    i < LENGTH ls ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f (EL i ls)) = SOME (EL i vs)``,
  rpt strip_tac >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (`LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
      simp[MAP_ZIP]) >>
  `LENGTH (MAP f ls) = LENGTH ls` by simp[LENGTH_MAP] >>
  simp[MEM_ZIP] >>
  qexists_tac `i` >> simp[EL_MAP]);
val alookup_zip_map_option_lookup_none = prove (``∀ls vs n ns f.
    INJ f (domain ns) UNIV ∧
    n ∈ domain ns ∧
    ¬MEM n ls ∧
    (∀v. MEM v ls ⇒ v ∈ domain ns) ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f n) = NONE``,
  rpt strip_tac >>
  Cases_on `ALOOKUP (ZIP (MAP f ls, vs)) (f n)` >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  `LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
  fs[MEM_ZIP] >>
  `f n = f (EL n' ls)` by
    (`EL n' (MAP f ls) = f (EL n' ls)` by (irule EL_MAP >> simp[]) >>
     fs[]) >>
  `MEM (EL n' ls) ls` by (simp[MEM_EL] >> qexists_tac `n'` >> simp[]) >>
  `EL n' ls ∈ domain ns` by (first_x_assum irule >> simp[]) >>
  `EL n' ls = n` by (
    qpat_x_assum `INJ f _ _` mp_tac >>
    simp[INJ_DEF] >> strip_tac >>
    first_x_assum irule >> simp[]) >>
  fs[]);
val evaluate_ssa_reconcile = prove (``ssa_locals_rel na cur_ssa st_locs cst.locals ∧
  INJ (option_lookup tgt_ssa) (domain ns) UNIV ⇒
  ∃cst'.
    evaluate (ssa_reconcile cur_ssa tgt_ssa ns, cst) = (NONE, cst') ∧
    word_state_eq_rel cst cst' ∧
    strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs cst'.locals``,
  rpt strip_tac >>
  simp[ssa_reconcile_def] >>
  qmatch_goalsub_abbrev_tac `if moves = [] then Skip else _` >>
  `moves = MAP (λv. (option_lookup tgt_ssa v, THE (lookup v cur_ssa)))
    (FILTER (λv. case lookup v cur_ssa of
                 | NONE => F
                 | SOME cv => option_lookup tgt_ssa v ≠ cv)
       (MAP FST (toAList ns)))` by
    (unabbrev_all_tac >> simp[ssa_reconcile_moves_eq]) >>
  qmatch_asmsub_abbrev_tac `MAP _ filtered_vars` >>
  `ALL_DISTINCT filtered_vars` by
    (unabbrev_all_tac >> simp[ssa_reconcile_filtered_all_distinct]) >>
  `∀v. MEM v filtered_vars ⇒ v ∈ domain ns ∧
       ∃cv. lookup v cur_ssa = SOME cv ∧ option_lookup tgt_ssa v ≠ cv ∧
            THE (lookup v cur_ssa) = cv` by
    (unabbrev_all_tac >>
     simp[MEM_FILTER, MEM_MAP, MEM_toAList, PULL_EXISTS, EXISTS_PROD] >>
     rpt strip_tac >>
     Cases_on `lookup v cur_ssa` >> fs[domain_lookup]) >>
  `ALL_DISTINCT (MAP (option_lookup tgt_ssa) filtered_vars)` by
    (match_mp_tac ALL_DISTINCT_MAP_INJ >>
     conj_tac >- (rw[] >> res_tac >> fs[INJ_DEF]) >>
     simp[]) >>
  Cases_on `moves = []`
  >- (
  simp[evaluate_def, word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  `filtered_vars = []` by (Cases_on `filtered_vars` >> fs[]) >>
  `option_lookup tgt_ssa n = cv` by (
    qpat_x_assum `filtered_vars = _` mp_tac >>
    unabbrev_all_tac >>
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, MEM_toAList, EXISTS_PROD,
         PULL_EXISTS] >>
    fs[domain_lookup] >>
    disch_then drule >>
    simp[]) >>
  simp[]
)
  >- (
  simp[evaluate_def] >>
  `MAP FST moves = MAP (option_lookup tgt_ssa) filtered_vars ∧
   MAP SND moves = MAP (λv. THE (lookup v cur_ssa)) filtered_vars` by
    (qpat_x_assum `moves = MAP _ _` SUBST1_TAC >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[MAP_EQ_f]) >>
  simp[] >>
  `∀v. MEM v filtered_vars ⇒
       ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val` by (
    rpt strip_tac >> res_tac >>
    fs[ssa_locals_rel_def] >>
    res_tac >> fs[domain_lookup]) >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) filtered_vars) cst
          = SOME vs ∧
        LENGTH vs = LENGTH filtered_vars ∧
        ∀i. i < LENGTH filtered_vars ⇒
            lookup (THE (lookup (EL i filtered_vars) cur_ssa)) cst.locals =
              SOME (EL i vs)`
    by (match_mp_tac ssa_reconcile_get_vars_lemma >> simp[]) >>
  qexists_tac
    `cst with locals := alist_insert
       (MAP (option_lookup tgt_ssa) filtered_vars) vs cst.locals` >>
  simp[set_vars_def, MAP_MAP_o, combinTheory.o_DEF, GSYM (SF ETA_ss)] >>
  simp[word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  simp[lookup_alist_insert] >>
  Cases_on `option_lookup tgt_ssa n = cv`
  >- (
    (* Case A: not in filtered_vars *)
    `¬MEM n filtered_vars` by (
      strip_tac >> res_tac >> fs[]) >>
    `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
       (option_lookup tgt_ssa n) = NONE` by (
      qspecl_then [`filtered_vars`, `vs`, `n`, `ns`, `option_lookup tgt_ssa`]
        mp_tac alookup_zip_map_option_lookup_none >>
      impl_tac
      >- (simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
      simp[]) >>
    fs[]) >>
  (* Case B: in filtered_vars *)
  `MEM n filtered_vars` by (
    unabbrev_all_tac >>
    simp[MEM_FILTER, MEM_MAP, MEM_toAList, EXISTS_PROD] >>
    fs[domain_lookup] >> metis_tac[]) >>
  `∃i. i < LENGTH filtered_vars ∧ EL i filtered_vars = n` by metis_tac[MEM_EL] >>
  `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
     (option_lookup tgt_ssa n) = SOME (EL i vs)` by (
    qpat_x_assum `EL i filtered_vars = n` (assume_tac o GSYM) >>
    simp[] >>
    irule alookup_zip_map_some >>
    simp[]) >>
  simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  impl_tac >- simp[] >>
  simp[] >> rw[]
));
val reconcile_empty = prove (``ssa_locals_rel na cur_ssa st_locs cst.locals ∧
  INJ (option_lookup tgt_ssa) (domain ns) UNIV ∧ FILTER (λ(a,b). a ≠ b) (FLAT (MAP (λv. case lookup v cur_ssa of NONE => [] | SOME cv => [(option_lookup tgt_ssa v,cv)]) (MAP FST (toAList ns)))) = [] ⇒
  ∃cst'.
    evaluate (ssa_reconcile cur_ssa tgt_ssa ns, cst) = (NONE, cst') ∧
    word_state_eq_rel cst cst' ∧
    strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs cst'.locals``, rpt strip_tac >> match_mp_tac evaluate_ssa_reconcile >> simp[]);
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "re_original_full" evaluate_ssa_reconcile;
val _ = out "re_empty_full" reconcile_empty;
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(free_vars(concl th))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "re_type_na" "na" reconcile_empty;
val _ = ty "re_type_cur_ssa" "cur_ssa" reconcile_empty;
val _ = ty "re_type_tgt_ssa" "tgt_ssa" reconcile_empty;
val _ = ty "re_type_st_locs" "st_locs" reconcile_empty;
val _ = ty "re_type_cst" "cst" reconcile_empty;
val _ = ty "re_type_ns" "ns" reconcile_empty;
