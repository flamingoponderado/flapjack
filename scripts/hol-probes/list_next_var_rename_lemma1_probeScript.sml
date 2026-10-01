load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocTheory word_allocProofTheory listTheory arithmeticTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val original_lemma = prove (``∀ls ssa na ls' ssa' na'.
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
val _ = (print "lnvr1_original_statement="; print_term (concl original_lemma); print "\n");
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val _ = out "lnvr1_empty" ``let (ns,t,n) = list_next_var_rename [] (fromAList [(9,99)]) 5 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+5) (COUNT_LIST (LENGTH [])),n=5+4*LENGTH [])``;
val _ = out "lnvr1_duplicates" ``let (ns,t,n) = list_next_var_rename [1;2;1] (fromAList [(9,99);(1,88)]) 5 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+5) (COUNT_LIST (LENGTH [1;2;1])),n=5+4*LENGTH [1;2;1])``;
val _ = out "lnvr1_invalid" ``let (ns,t,n) = list_next_var_rename [0;4] (BN LN LN) 0 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+0) (COUNT_LIST (LENGTH [0;4])),n=0+4*LENGTH [0;4])``;
val _ = out "lnvr1_collision" ``let (ns,t,n) = list_next_var_rename [9] (fromAList [(9,99);(1,88)]) 101 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+101) (COUNT_LIST (LENGTH [9])),n=101+4*LENGTH [9])``;
val _ = out "lnvr1_zero_duplicates" ``let (ns,t,n) = list_next_var_rename [2;2;2] (LN) 0 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+0) (COUNT_LIST (LENGTH [2;2;2])),n=0+4*LENGTH [2;2;2])``;
val _ = out "lnvr1_odd_start" ``let (ns,t,n) = list_next_var_rename [100;0;4] (LN) 3 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+3) (COUNT_LIST (LENGTH [100;0;4])),n=3+4*LENGTH [100;0;4])``;
val _ = out "lnvr1_huge" ``let (ns,t,n) = list_next_var_rename [1208925819614629174706176;1208925819614629174706176] (LN) 1208925819614629174706176 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+1208925819614629174706176) (COUNT_LIST (LENGTH [1208925819614629174706176;1208925819614629174706176])),n=1208925819614629174706176+4*LENGTH [1208925819614629174706176;1208925819614629174706176])``;
val _ = out "lnvr1_range" ``let (ns,t,n) = list_next_var_rename [0;1;2;3;4;5] (LN) 2 in (ns,MAP (\k.lookup k t) [0;1;2;4;9;100;1208925819614629174706176],n,ALL_DISTINCT ns,ns=MAP (\x.4*x+2) (COUNT_LIST (LENGTH [0;1;2;3;4;5])),n=2+4*LENGTH [0;1;2;3;4;5])``;
