load "bossLib";
load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble arithmeticTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val limit_numeric = prove (``!x:num. is_alloc_var (x+(4-x MOD 4)+1) /\ x < x+(4-x MOD 4)+1``,
  gen_tac >> reverse CONJ_TAC >- DECIDE_TAC >>
  simp[is_alloc_var_def] >>
  assume_tac arithmeticTheory.MOD_PLUS>>
  `(x + (4 - x MOD 4)) MOD 4 = 0` by
   (`x MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
    `(x MOD 4 = 0) ∨ (x MOD 4 = 1) ∨ (x MOD 4 = 2) ∨ (x MOD 4 = 3)` by
      DECIDE_TAC>>
    full_simp_tac std_ss [EVAL “0<4:num”]>>
    (*Fastest way I could find*)
    `(0 MOD 4 = 0) ∧
    (1 MOD 4 = 1) ∧
    (2 MOD 4 = 2) ∧
    (3 MOD 4 = 3) ∧
    (4 MOD 4 = 0)` by full_simp_tac(srw_ss())[]>>
    `((0+0)MOD 4 = 0) ∧
    ((1+3)MOD 4 = 0) ∧
    ((2+2)MOD 4 = 0) ∧
    ((3+1)MOD 4 = 0)` by full_simp_tac(srw_ss())[]>>
    metis_tac[]) >>
  full_simp_tac std_ss [EVAL “0<4:num”]>>
  first_x_assum(qspecl_then [`4`,`x+(4- x MOD 4)`,`1`] assume_tac)>>
  pop_assum sym_sub_tac>>
  full_simp_tac(srw_ss())[]);
val _ = (print "la_original_numeric_proof=";print_thm limit_numeric;print "\n");
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = out "la_0" ``let x = 0:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_1" ``let x = 1:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_2" ``let x = 2:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_3" ``let x = 3:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_4" ``let x = 4:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_7" ``let x = 7:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_8" ``let x = 8:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_15" ``let x = 15:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_16" ``let x = 16:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_1208925819614629174706176" ``let x = 1208925819614629174706176:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_1208925819614629174706177" ``let x = 1208925819614629174706177:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_1208925819614629174706178" ``let x = 1208925819614629174706178:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
val _ = out "la_1208925819614629174706179" ``let x = 1208925819614629174706179:num in (x+(4-x MOD 4)+1, is_alloc_var (x+(4-x MOD 4)+1), x < x+(4-x MOD 4)+1, (x+(4-x MOD 4)) MOD 4)``;
