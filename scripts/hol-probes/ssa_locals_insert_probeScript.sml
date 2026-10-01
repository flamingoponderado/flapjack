load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory sptreeTheory reg_allocTheory;
val statement = ``ssa_locals_rel na ssa stloc cstloc ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stloc) (insert na w cstloc)``;
val result = prove(statement,
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
val _ = print "fi_full=";
val _ = print_thm result;
val _ = print "\n";
fun out label name =
 let val term = valOf(List.find (fn t => fst(dest_var t) = name) (free_vars statement))
 in print(label ^ "="); print_type(type_of term); print "\n" end;
val _ = out "fi_source_type" "stloc";
val _ = out "fi_target_type" "cstloc";
val _ = out "fi_value_type" "w";

val setVarStatement = ``ssa_locals_rel na ssa stl cstl ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stl) (insert na w cstl)``;
val setVarResult = prove(setVarStatement,
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
val _ = print "fi_set_var_full=";
val _ = print_thm setVarResult;
val _ = print "\n";
val empty = Q.prove(
 `ssa_locals_rel (1+4) (insert 0 1 LN) (insert 0 F LN) (insert 1 F LN)`,
 match_mp_tac result >>
 simp[ssa_locals_rel_def,ssa_map_ok_def,lookup_def,lookup_insert,domain_lookup,is_alloc_var_def,is_phy_var_def]);
val _ = print "fi_empty="; val _ = print_thm empty; val _ = print "\n";
val preserve = Q.prove(
 `ssa_locals_rel (8+4) (insert 0 8 (fromAList [(1,5)]))
   (insert 0 F (fromAList [(1,T)])) (insert 8 F (fromAList [(5,T)]))`,
 match_mp_tac result >>
 simp[ssa_locals_rel_def,ssa_map_ok_def,lookup_def,lookup_insert,domain_lookup,is_alloc_var_def,is_phy_var_def]);
val _ = print "fi_preserve="; val _ = print_thm preserve; val _ = print "\n";
