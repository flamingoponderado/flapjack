load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocTheory word_allocProofTheory wordLangTheory wordConvsTheory reg_allocTheory sptreeTheory;
val _ = Globals.linewidth := 1000;
val props_source = GEN_ALL (prove (``  limit_var prog = lim ⇒
  is_alloc_var lim ∧
  every_var (λx. x< lim) prog``,
  reverse (srw_tac[][limit_var_def,is_alloc_var_def])
  >-
    (qspec_then `prog` assume_tac max_var_max >>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[Abbr`x'`]>>
    DECIDE_TAC)
  >>
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
  full_simp_tac(srw_ss())[]));
val _ = (print "lp_full_source_replay=";print_thm props_source;print "\n");
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
val _ = out "lp_residue0" ``let p = (Assign 0 (Const 0w):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_residue1" ``let p = (Assign 1 (Const 0w):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_residue2" ``let p = (Assign 2 (Const 0w):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_residue3" ``let p = (Assign 3 (Const 0w):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_residue4" ``let p = (Assign 4 (Const 0w):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_skip1" ``let p = (Skip:1 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_seven" ``let p = (Assign 7 (Const 0w):64 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_eight" ``let p = (Assign 8 (Const 0w):80 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_ignored16" ``let p = (Inst (Mem Load16 999 (Addr 777 3w)):64 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_tail_handler" ``let p = (Call NONE (SOME 999) [] (SOME (1000,Assign 1001 (Var 1002),1003,1004)):32 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_call_body" ``let p = (Call (SOME ([1],(LN,LN),Assign 26 (Const 0w),7,8)) (SOME 0) [] NONE:64 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
val _ = out "lp_huge" ``let p = (Assign 1208925819614629174706176 (Var 7):1 wordLang$prog) in (max_var p,limit_var p,is_alloc_var (limit_var p),every_var (\x.x<limit_var p) p)``;
