load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val get_vars_list_insert_eq_gen = prove (``  !ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars ls (st with locals := alist_insert (a++ls) (b++x) locs) = SOME x``,
  ho_match_mp_tac alist_insert_ind>>
  srw_tac[][]>- (full_simp_tac(srw_ss())[get_vars_def])>>
  full_simp_tac(srw_ss())[get_vars_def,get_var_def,lookup_alist_insert]>>
  `LENGTH (ls::ls') = LENGTH (x::x')` by full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC rich_listTheory.ZIP_APPEND>>
  ntac 9 (pop_assum (SUBST1_TAC o SYM))>>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND]>>
  first_assum(qspec_then `ls` assume_tac)>>full_simp_tac(srw_ss())[]>>
  `ALOOKUP (ZIP (a,b)) ls = NONE` by metis_tac[ALOOKUP_NONE,MEM_MAP,MAP_ZIP]>>
  full_simp_tac(srw_ss())[]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  `LENGTH (a++[ls]) = LENGTH (b++[x])` by full_simp_tac(srw_ss())[]>> rev_full_simp_tac(srw_ss())[]>>
  `a++[ls]++ls' = a++ls::ls' /\ b++[x]++x' = b++x::x'` by full_simp_tac(srw_ss())[]>>
  ntac 2 (pop_assum SUBST_ALL_TAC)>> full_simp_tac(srw_ss())[]);
val _ = print "get_vars_list_insert_eq_gen_full="; val _ = print_thm get_vars_list_insert_eq_gen; val _ = print "\n";
val get_vars_set_vars_eq = prove (``  ∀ls x.
  ALL_DISTINCT ls ∧ LENGTH x = LENGTH ls ⇒
  get_vars ls (set_vars ls x cst) = SOME x``,
  full_simp_tac(srw_ss())[get_vars_def,set_vars_def]>>srw_tac[][]>>
  Q.ISPECL_THEN [`cst`,`ls`,`x`,`cst.locals`,`[]:num list`
    ,`[]:'a word_loc list`] mp_tac (GEN_ALL get_vars_list_insert_eq_gen)>>
  impl_tac>>full_simp_tac(srw_ss())[]);
val _ = print "get_vars_set_vars_eq_full="; val _ = print_thm get_vars_set_vars_eq; val _ = print "\n";
val result = get_vars_list_insert_eq_gen;
fun out label name = let val vs = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vs) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "gvi_type_st" "st";
val _ = out "gvi_type_ls" "ls";
val _ = out "gvi_type_x" "x";
val _ = out "gvi_type_locs" "locs";
val _ = out "gvi_type_a" "a";
val _ = out "gvi_type_b" "b";
val result = get_vars_set_vars_eq;
fun out label name = let val vs = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vs) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "gsv_type_cst" "cst";
val _ = out "gsv_type_ls" "ls";
val _ = out "gsv_type_x" "x";
