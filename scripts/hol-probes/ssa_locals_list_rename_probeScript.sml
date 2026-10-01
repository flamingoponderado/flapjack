load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val list_next_var_rename_lemma_1 = prove (``  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧
  na' = na + 4* len``,
  Induct>>
  full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  srw_tac[][]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  res_tac
  >-
    (`∀x. MEM x q ⇒ na < x` by
      (srw_tac[][MEM_MAP]>>DECIDE_TAC)>>
    qpat_x_assum`A = ls'` (sym_sub_tac)>>
    `¬ MEM na q` by
      (SPOSE_NOT_THEN assume_tac>>
      res_tac>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[ALL_DISTINCT])
  >-
    (full_simp_tac(srw_ss())[MAP_MAP_o]>>
    qpat_x_assum`A = ls'` sym_sub_tac>>
    full_simp_tac(srw_ss())[MAP_EQ_f]>>srw_tac[][]>>
    DECIDE_TAC)
  >>
    DECIDE_TAC);
val ssa_map_ok_extend = prove (``  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC);
val ssa_locals_rel_insert = prove (``  ssa_locals_rel na ssa stloc cstloc ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stloc) (insert na w cstloc)``,
  srw_tac[][ssa_locals_rel_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=n`>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >-
    (res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,ssa_map_ok_def]>>
    first_x_assum(qspecl_then[`x`,`v`]assume_tac)>>
    (*Next part is a key reasoning step --
      We only have alloc_vars < na in the range of ssa
      Otherwise, the new one may overwrite an old mapping
    *)
    rev_full_simp_tac(srw_ss())[]>>
    `v ≠ na` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[])
  >-
    DECIDE_TAC
  >>
    (*Finally, this illustrates need for <na assumption on st.locals*)
    full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];
val result = prove (``  ∀xs ssa na stloc cstloc ys ssa' na' ls.
  list_next_var_rename xs ssa na = (ys,ssa',na') ∧
  ssa_locals_rel na ssa stloc cstloc ∧
  ssa_map_ok na ssa ∧
  LENGTH xs = LENGTH ls ∧
  EVERY (λx. x < na) xs ∧
  ALL_DISTINCT xs ∧
  ¬is_phy_var na ⇒
  ssa_locals_rel na' ssa' (alist_insert xs ls stloc) (alist_insert ys ls cstloc)``,
  Induct>>rw[list_next_var_rename_def,quantHeuristicsTheory.LIST_LENGTH_COMPARE_SUC]>>
  rpt(pairarg_tac>>gvs[])>>
  gvs[alist_insert_def,next_var_rename_def]>>
  last_x_assum drule>>
  rename1`insert na _ (alist_insert yss _ _)`>>
  `¬MEM na yss` by (
    drule list_next_var_rename_lemma_1>>
    rw[]>>
    simp[MEM_MAP])>>
  simp[GSYM alist_insert_pull_insert]>>
  disch_then irule>>
  rw[]
  >-
    is_phy_var_tac
  >- (
    irule EVERY_MONOTONIC>>
    first_x_assum (irule_at Any)>>
    simp[])
  >-
    simp[ssa_map_ok_extend]>>
  irule ssa_locals_rel_insert>>
  simp[]);
val _ = print "lr_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (fst(strip_forall(concl result)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "lr_type_xs" "xs";
val _ = out "lr_type_ssa" "ssa";
val _ = out "lr_type_na" "na";
val _ = out "lr_type_stloc" "stloc";
val _ = out "lr_type_cstloc" "cstloc";
val _ = out "lr_type_ys" "ys";
val _ = out "lr_type_ssaOut" "ssa'";
val _ = out "lr_type_naOut" "na'";
val _ = out "lr_type_ls" "ls";
