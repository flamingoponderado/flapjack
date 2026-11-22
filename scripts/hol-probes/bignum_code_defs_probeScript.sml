(* Untyped right-hand sides of the 64 code constants that word_bignum's
   to_deep defines (Define `NAME_code = ...`), in sorted name order, for the
   Lean generator scripts/generate-bignum-mini.py. Each RHS mentions the
   other generated code constants by name, as HOL's definitions do. The
   untyped conclusions of the 60 NAME_corr_thm theorems of word_bignumProof
   follow, for the corr-theorem generator scripts/generate-bignum-corr.py. *)
load "word_bignumProofTheory"; load "wordsLib";
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
fun emit_corr name =
  let val th = fetch "word_bignumProof" name
  in if null (hyp th) then
       (print (name ^ "="); print_term (concl th); print "\n")
     else raise Fail (name ^ " has hypotheses")
  end;
val _ = emit_corr "mc_add1_call_corr_thm";
val _ = emit_corr "mc_add1_corr_thm";
val _ = emit_corr "mc_add_corr_thm";
val _ = emit_corr "mc_add_loop1_corr_thm";
val _ = emit_corr "mc_add_loop2_corr_thm";
val _ = emit_corr "mc_add_loop_corr_thm";
val _ = emit_corr "mc_adj_cmp_corr_thm";
val _ = emit_corr "mc_adjust_aux_corr_thm";
val _ = emit_corr "mc_calc_d_corr_thm";
val _ = emit_corr "mc_cmp2_corr_thm";
val _ = emit_corr "mc_cmp3_corr_thm";
val _ = emit_corr "mc_cmp_corr_thm";
val _ = emit_corr "mc_cmp_mul2_corr_thm";
val _ = emit_corr "mc_compare_corr_thm";
val _ = emit_corr "mc_copy_down_corr_thm";
val _ = emit_corr "mc_copy_over_corr_thm";
val _ = emit_corr "mc_div0_corr_thm";
val _ = emit_corr "mc_div1_corr_thm";
val _ = emit_corr "mc_div2_corr_thm";
val _ = emit_corr "mc_div3_corr_thm";
val _ = emit_corr "mc_div_adjust_corr_thm";
val _ = emit_corr "mc_div_corr_thm";
val _ = emit_corr "mc_div_guess_corr_thm";
val _ = emit_corr "mc_div_loop_corr_thm";
val _ = emit_corr "mc_div_r1_corr_thm";
val _ = emit_corr "mc_div_sub1_corr_thm";
val _ = emit_corr "mc_div_sub_aux1_corr_thm";
val _ = emit_corr "mc_div_sub_aux_corr_thm";
val _ = emit_corr "mc_div_sub_call_corr_thm";
val _ = emit_corr "mc_div_sub_corr_thm";
val _ = emit_corr "mc_div_sub_loop_corr_thm";
val _ = emit_corr "mc_div_test_corr_thm";
val _ = emit_corr "mc_fix_corr_thm";
val _ = emit_corr "mc_iadd1_corr_thm";
val _ = emit_corr "mc_iadd2_corr_thm";
val _ = emit_corr "mc_iadd3_corr_thm";
val _ = emit_corr "mc_iadd_corr_thm";
val _ = emit_corr "mc_idiv0_corr_thm";
val _ = emit_corr "mc_idiv_corr_thm";
val _ = emit_corr "mc_idiv_mod_header_corr_thm";
val _ = emit_corr "mc_imul1_corr_thm";
val _ = emit_corr "mc_imul_corr_thm";
val _ = emit_corr "mc_iop_corr_thm";
val _ = emit_corr "mc_isub_flip_corr_thm";
val _ = emit_corr "mc_mul_by_single2_corr_thm";
val _ = emit_corr "mc_mul_by_single_corr_thm";
val _ = emit_corr "mc_mul_corr_thm";
val _ = emit_corr "mc_mul_pass_corr_thm";
val _ = emit_corr "mc_mul_zero_corr_thm";
val _ = emit_corr "mc_simple_div1_corr_thm";
val _ = emit_corr "mc_simple_div_corr_thm";
val _ = emit_corr "mc_single_div_corr_thm";
val _ = emit_corr "mc_single_mul_add_corr_thm";
val _ = emit_corr "mc_single_mul_corr_thm";
val _ = emit_corr "mc_sub1_corr_thm";
val _ = emit_corr "mc_sub_corr_thm";
val _ = emit_corr "mc_sub_loop1_corr_thm";
val _ = emit_corr "mc_sub_loop2_corr_thm";
val _ = emit_corr "mc_sub_loop_corr_thm";
val _ = emit_corr "mc_top_two_corr_thm";
