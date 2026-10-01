load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_locals_rel_ignore_set_var = prove (``ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  is_phy_var v
  ⇒
  ssa_locals_rel na ssa st.locals (set_var v a cst).locals``,
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def,set_var_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  metis_tac[]);
val _ = print "ph_set_full=";
val _ = print_thm ssa_locals_rel_ignore_set_var;
val _ = print "\n";
fun types_ph_set label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (free_vars(concl ssa_locals_rel_ignore_set_var))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = types_ph_set "ph_set_type_st" "st";
val _ = types_ph_set "ph_set_type_cst" "cst";
val ssa_locals_rel_ignore_list_insert = prove (``ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  EVERY is_phy_var ls ∧
  LENGTH ls = LENGTH x
  ⇒
  ssa_locals_rel na ssa st.locals (alist_insert ls x cst.locals)``,
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def]>>
  full_simp_tac(srw_ss())[domain_alist_insert,lookup_alist_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  res_tac>>
  `ALOOKUP (ZIP(ls,x)) v = NONE` by
    (srw_tac[][ALOOKUP_FAILS,MEM_ZIP]>>
    metis_tac[EVERY_EL])>>
  full_simp_tac(srw_ss())[]);
val _ = print "ph_list_full=";
val _ = print_thm ssa_locals_rel_ignore_list_insert;
val _ = print "\n";
fun types_ph_list label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (free_vars(concl ssa_locals_rel_ignore_list_insert))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = types_ph_list "ph_list_type_st" "st";
val _ = types_ph_list "ph_list_type_cst" "cst";
