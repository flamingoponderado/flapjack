(* Untyped right-hand sides of the 64 code constants that word_bignum's
   to_deep defines (Define `NAME_code = ...`), in sorted name order, for the
   Lean generator scripts/generate-bignum-mini.py. Each RHS mentions the
   other generated code constants by name, as HOL's definitions do. *)
load "word_bignumTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun emit name =
  let val th = fetch "word_bignum" name
  in if null (hyp th) then
       (print (name ^ "="); print_term (rhs (concl th)); print "\n")
     else raise Fail (name ^ " has hypotheses")
  end;
val _ = emit "mc_add1_call_code_def";
val _ = emit "mc_add1_code_def";
val _ = emit "mc_add_code_def";
val _ = emit "mc_add_loop1_code_def";
val _ = emit "mc_add_loop2_code_def";
val _ = emit "mc_add_loop_code_def";
val _ = emit "mc_adj_cmp_code_def";
val _ = emit "mc_adjust_aux_code_def";
val _ = emit "mc_calc_d_code_def";
val _ = emit "mc_cmp2_code_def";
val _ = emit "mc_cmp3_code_def";
val _ = emit "mc_cmp_code_def";
val _ = emit "mc_cmp_mul2_code_def";
val _ = emit "mc_compare_code_def";
val _ = emit "mc_copy_down_code_def";
val _ = emit "mc_copy_over_code_def";
val _ = emit "mc_div0_code_def";
val _ = emit "mc_div1_code_def";
val _ = emit "mc_div2_code_def";
val _ = emit "mc_div3_code_def";
val _ = emit "mc_div_adjust_code_def";
val _ = emit "mc_div_code_def";
val _ = emit "mc_div_guess_code_def";
val _ = emit "mc_div_loop_code_def";
val _ = emit "mc_div_r1_code_def";
val _ = emit "mc_div_sub1_code_def";
val _ = emit "mc_div_sub_aux1_code_def";
val _ = emit "mc_div_sub_aux_code_def";
val _ = emit "mc_div_sub_call_code_def";
val _ = emit "mc_div_sub_code_def";
val _ = emit "mc_div_sub_loop_code_def";
val _ = emit "mc_div_test_code_def";
val _ = emit "mc_fac_code_def";
val _ = emit "mc_fac_final_code_def";
val _ = emit "mc_fac_init_code_def";
val _ = emit "mc_fix_code_def";
val _ = emit "mc_iadd1_code_def";
val _ = emit "mc_iadd2_code_def";
val _ = emit "mc_iadd3_code_def";
val _ = emit "mc_iadd_code_def";
val _ = emit "mc_idiv0_code_def";
val _ = emit "mc_idiv_code_def";
val _ = emit "mc_idiv_mod_header_code_def";
val _ = emit "mc_imul1_code_def";
val _ = emit "mc_imul_code_def";
val _ = emit "mc_iop_code_def";
val _ = emit "mc_isub_flip_code_def";
val _ = emit "mc_mul_by_single2_code_def";
val _ = emit "mc_mul_by_single_code_def";
val _ = emit "mc_mul_code_def";
val _ = emit "mc_mul_pass_code_def";
val _ = emit "mc_mul_zero_code_def";
val _ = emit "mc_simple_div1_code_def";
val _ = emit "mc_simple_div_code_def";
val _ = emit "mc_single_div_code_def";
val _ = emit "mc_single_mul_add_code_def";
val _ = emit "mc_single_mul_code_def";
val _ = emit "mc_sub1_code_def";
val _ = emit "mc_sub_code_def";
val _ = emit "mc_sub_loop1_code_def";
val _ = emit "mc_sub_loop2_code_def";
val _ = emit "mc_sub_loop_code_def";
val _ = emit "mc_top_two_code_def";
val _ = emit "mc_use_fac_code_def";
