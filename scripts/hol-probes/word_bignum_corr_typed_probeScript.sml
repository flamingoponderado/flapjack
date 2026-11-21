(* Typed captures of the theorems and definitions that word_bignumProof's
   derive_corr_thm and word_bignum's to_deep generate dynamically:
   every NAME_corr_thm saved by derive_corr_thm (save_thm (name ^ "_corr_thm"))
   and every NAME_code_def defined by to_deep (Define `NAME_code = ...`).
   They are not literal source declarations, so they are read from the
   compiled theories. Rows are emitted in sorted name order under static
   labels NAME_typed. *)
load "word_bignumProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;

fun emit label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun has_suffix suf s =
  String.size s >= String.size suf andalso
  String.extract (s, String.size s - String.size suf, NONE) = suf;

fun sorted_names thy suf =
  Listsort.sort String.compare
    (List.filter (has_suffix suf) (map #1 (DB.thms thy)));

(* The static name lists below are checked against the theory databases, so a
   source change that adds or removes a generated name fails loudly. *)
val code_names = [
  "mc_add1_call_code_def",
  "mc_add1_code_def",
  "mc_add_code_def",
  "mc_add_loop1_code_def",
  "mc_add_loop2_code_def",
  "mc_add_loop_code_def",
  "mc_adj_cmp_code_def",
  "mc_adjust_aux_code_def",
  "mc_calc_d_code_def",
  "mc_cmp2_code_def",
  "mc_cmp3_code_def",
  "mc_cmp_code_def",
  "mc_cmp_mul2_code_def",
  "mc_compare_code_def",
  "mc_copy_down_code_def",
  "mc_copy_over_code_def",
  "mc_div0_code_def",
  "mc_div1_code_def",
  "mc_div2_code_def",
  "mc_div3_code_def",
  "mc_div_adjust_code_def",
  "mc_div_code_def",
  "mc_div_guess_code_def",
  "mc_div_loop_code_def",
  "mc_div_r1_code_def",
  "mc_div_sub1_code_def",
  "mc_div_sub_aux1_code_def",
  "mc_div_sub_aux_code_def",
  "mc_div_sub_call_code_def",
  "mc_div_sub_code_def",
  "mc_div_sub_loop_code_def",
  "mc_div_test_code_def",
  "mc_fac_code_def",
  "mc_fac_final_code_def",
  "mc_fac_init_code_def",
  "mc_fix_code_def",
  "mc_iadd1_code_def",
  "mc_iadd2_code_def",
  "mc_iadd3_code_def",
  "mc_iadd_code_def",
  "mc_idiv0_code_def",
  "mc_idiv_code_def",
  "mc_idiv_mod_header_code_def",
  "mc_imul1_code_def",
  "mc_imul_code_def",
  "mc_iop_code_def",
  "mc_isub_flip_code_def",
  "mc_mul_by_single2_code_def",
  "mc_mul_by_single_code_def",
  "mc_mul_code_def",
  "mc_mul_pass_code_def",
  "mc_mul_zero_code_def",
  "mc_simple_div1_code_def",
  "mc_simple_div_code_def",
  "mc_single_div_code_def",
  "mc_single_mul_add_code_def",
  "mc_single_mul_code_def",
  "mc_sub1_code_def",
  "mc_sub_code_def",
  "mc_sub_loop1_code_def",
  "mc_sub_loop2_code_def",
  "mc_sub_loop_code_def",
  "mc_top_two_code_def",
  "mc_use_fac_code_def"];
val corr_names = [
  "mc_add1_call_corr_thm",
  "mc_add1_corr_thm",
  "mc_add_corr_thm",
  "mc_add_loop1_corr_thm",
  "mc_add_loop2_corr_thm",
  "mc_add_loop_corr_thm",
  "mc_adj_cmp_corr_thm",
  "mc_adjust_aux_corr_thm",
  "mc_calc_d_corr_thm",
  "mc_cmp2_corr_thm",
  "mc_cmp3_corr_thm",
  "mc_cmp_corr_thm",
  "mc_cmp_mul2_corr_thm",
  "mc_compare_corr_thm",
  "mc_copy_down_corr_thm",
  "mc_copy_over_corr_thm",
  "mc_div0_corr_thm",
  "mc_div1_corr_thm",
  "mc_div2_corr_thm",
  "mc_div3_corr_thm",
  "mc_div_adjust_corr_thm",
  "mc_div_corr_thm",
  "mc_div_guess_corr_thm",
  "mc_div_loop_corr_thm",
  "mc_div_r1_corr_thm",
  "mc_div_sub1_corr_thm",
  "mc_div_sub_aux1_corr_thm",
  "mc_div_sub_aux_corr_thm",
  "mc_div_sub_call_corr_thm",
  "mc_div_sub_corr_thm",
  "mc_div_sub_loop_corr_thm",
  "mc_div_test_corr_thm",
  "mc_fix_corr_thm",
  "mc_iadd1_corr_thm",
  "mc_iadd2_corr_thm",
  "mc_iadd3_corr_thm",
  "mc_iadd_corr_thm",
  "mc_idiv0_corr_thm",
  "mc_idiv_corr_thm",
  "mc_idiv_mod_header_corr_thm",
  "mc_imul1_corr_thm",
  "mc_imul_corr_thm",
  "mc_iop_corr_thm",
  "mc_isub_flip_corr_thm",
  "mc_mul_by_single2_corr_thm",
  "mc_mul_by_single_corr_thm",
  "mc_mul_corr_thm",
  "mc_mul_pass_corr_thm",
  "mc_mul_zero_corr_thm",
  "mc_simple_div1_corr_thm",
  "mc_simple_div_corr_thm",
  "mc_single_div_corr_thm",
  "mc_single_mul_add_corr_thm",
  "mc_single_mul_corr_thm",
  "mc_sub1_corr_thm",
  "mc_sub_corr_thm",
  "mc_sub_loop1_corr_thm",
  "mc_sub_loop2_corr_thm",
  "mc_sub_loop_corr_thm",
  "mc_top_two_corr_thm"];

val _ = if sorted_names "word_bignum" "_code_def" = code_names andalso
           sorted_names "word_bignumProof" "_corr_thm" = corr_names
        then () else raise Fail "generated name list changed";

val _ = print "word_bignum_corr_probe_begin=1\n";
val _ = emit "mc_add1_call_code_def_typed" (fetch "word_bignum" "mc_add1_call_code_def");
val _ = emit "mc_add1_code_def_typed" (fetch "word_bignum" "mc_add1_code_def");
val _ = emit "mc_add_code_def_typed" (fetch "word_bignum" "mc_add_code_def");
val _ = emit "mc_add_loop1_code_def_typed" (fetch "word_bignum" "mc_add_loop1_code_def");
val _ = emit "mc_add_loop2_code_def_typed" (fetch "word_bignum" "mc_add_loop2_code_def");
val _ = emit "mc_add_loop_code_def_typed" (fetch "word_bignum" "mc_add_loop_code_def");
val _ = emit "mc_adj_cmp_code_def_typed" (fetch "word_bignum" "mc_adj_cmp_code_def");
val _ = emit "mc_adjust_aux_code_def_typed" (fetch "word_bignum" "mc_adjust_aux_code_def");
val _ = emit "mc_calc_d_code_def_typed" (fetch "word_bignum" "mc_calc_d_code_def");
val _ = emit "mc_cmp2_code_def_typed" (fetch "word_bignum" "mc_cmp2_code_def");
val _ = emit "mc_cmp3_code_def_typed" (fetch "word_bignum" "mc_cmp3_code_def");
val _ = emit "mc_cmp_code_def_typed" (fetch "word_bignum" "mc_cmp_code_def");
val _ = emit "mc_cmp_mul2_code_def_typed" (fetch "word_bignum" "mc_cmp_mul2_code_def");
val _ = emit "mc_compare_code_def_typed" (fetch "word_bignum" "mc_compare_code_def");
val _ = emit "mc_copy_down_code_def_typed" (fetch "word_bignum" "mc_copy_down_code_def");
val _ = emit "mc_copy_over_code_def_typed" (fetch "word_bignum" "mc_copy_over_code_def");
val _ = emit "mc_div0_code_def_typed" (fetch "word_bignum" "mc_div0_code_def");
val _ = emit "mc_div1_code_def_typed" (fetch "word_bignum" "mc_div1_code_def");
val _ = emit "mc_div2_code_def_typed" (fetch "word_bignum" "mc_div2_code_def");
val _ = emit "mc_div3_code_def_typed" (fetch "word_bignum" "mc_div3_code_def");
val _ = emit "mc_div_adjust_code_def_typed" (fetch "word_bignum" "mc_div_adjust_code_def");
val _ = emit "mc_div_code_def_typed" (fetch "word_bignum" "mc_div_code_def");
val _ = emit "mc_div_guess_code_def_typed" (fetch "word_bignum" "mc_div_guess_code_def");
val _ = emit "mc_div_loop_code_def_typed" (fetch "word_bignum" "mc_div_loop_code_def");
val _ = emit "mc_div_r1_code_def_typed" (fetch "word_bignum" "mc_div_r1_code_def");
val _ = emit "mc_div_sub1_code_def_typed" (fetch "word_bignum" "mc_div_sub1_code_def");
val _ = emit "mc_div_sub_aux1_code_def_typed" (fetch "word_bignum" "mc_div_sub_aux1_code_def");
val _ = emit "mc_div_sub_aux_code_def_typed" (fetch "word_bignum" "mc_div_sub_aux_code_def");
val _ = emit "mc_div_sub_call_code_def_typed" (fetch "word_bignum" "mc_div_sub_call_code_def");
val _ = emit "mc_div_sub_code_def_typed" (fetch "word_bignum" "mc_div_sub_code_def");
val _ = emit "mc_div_sub_loop_code_def_typed" (fetch "word_bignum" "mc_div_sub_loop_code_def");
val _ = emit "mc_div_test_code_def_typed" (fetch "word_bignum" "mc_div_test_code_def");
val _ = emit "mc_fac_code_def_typed" (fetch "word_bignum" "mc_fac_code_def");
val _ = emit "mc_fac_final_code_def_typed" (fetch "word_bignum" "mc_fac_final_code_def");
val _ = emit "mc_fac_init_code_def_typed" (fetch "word_bignum" "mc_fac_init_code_def");
val _ = emit "mc_fix_code_def_typed" (fetch "word_bignum" "mc_fix_code_def");
val _ = emit "mc_iadd1_code_def_typed" (fetch "word_bignum" "mc_iadd1_code_def");
val _ = emit "mc_iadd2_code_def_typed" (fetch "word_bignum" "mc_iadd2_code_def");
val _ = emit "mc_iadd3_code_def_typed" (fetch "word_bignum" "mc_iadd3_code_def");
val _ = emit "mc_iadd_code_def_typed" (fetch "word_bignum" "mc_iadd_code_def");
val _ = emit "mc_idiv0_code_def_typed" (fetch "word_bignum" "mc_idiv0_code_def");
val _ = emit "mc_idiv_code_def_typed" (fetch "word_bignum" "mc_idiv_code_def");
val _ = emit "mc_idiv_mod_header_code_def_typed" (fetch "word_bignum" "mc_idiv_mod_header_code_def");
val _ = emit "mc_imul1_code_def_typed" (fetch "word_bignum" "mc_imul1_code_def");
val _ = emit "mc_imul_code_def_typed" (fetch "word_bignum" "mc_imul_code_def");
val _ = emit "mc_iop_code_def_typed" (fetch "word_bignum" "mc_iop_code_def");
val _ = emit "mc_isub_flip_code_def_typed" (fetch "word_bignum" "mc_isub_flip_code_def");
val _ = emit "mc_mul_by_single2_code_def_typed" (fetch "word_bignum" "mc_mul_by_single2_code_def");
val _ = emit "mc_mul_by_single_code_def_typed" (fetch "word_bignum" "mc_mul_by_single_code_def");
val _ = emit "mc_mul_code_def_typed" (fetch "word_bignum" "mc_mul_code_def");
val _ = emit "mc_mul_pass_code_def_typed" (fetch "word_bignum" "mc_mul_pass_code_def");
val _ = emit "mc_mul_zero_code_def_typed" (fetch "word_bignum" "mc_mul_zero_code_def");
val _ = emit "mc_simple_div1_code_def_typed" (fetch "word_bignum" "mc_simple_div1_code_def");
val _ = emit "mc_simple_div_code_def_typed" (fetch "word_bignum" "mc_simple_div_code_def");
val _ = emit "mc_single_div_code_def_typed" (fetch "word_bignum" "mc_single_div_code_def");
val _ = emit "mc_single_mul_add_code_def_typed" (fetch "word_bignum" "mc_single_mul_add_code_def");
val _ = emit "mc_single_mul_code_def_typed" (fetch "word_bignum" "mc_single_mul_code_def");
val _ = emit "mc_sub1_code_def_typed" (fetch "word_bignum" "mc_sub1_code_def");
val _ = emit "mc_sub_code_def_typed" (fetch "word_bignum" "mc_sub_code_def");
val _ = emit "mc_sub_loop1_code_def_typed" (fetch "word_bignum" "mc_sub_loop1_code_def");
val _ = emit "mc_sub_loop2_code_def_typed" (fetch "word_bignum" "mc_sub_loop2_code_def");
val _ = emit "mc_sub_loop_code_def_typed" (fetch "word_bignum" "mc_sub_loop_code_def");
val _ = emit "mc_top_two_code_def_typed" (fetch "word_bignum" "mc_top_two_code_def");
val _ = emit "mc_use_fac_code_def_typed" (fetch "word_bignum" "mc_use_fac_code_def");
val _ = emit "mc_add1_call_corr_thm_typed" (fetch "word_bignumProof" "mc_add1_call_corr_thm");
val _ = emit "mc_add1_corr_thm_typed" (fetch "word_bignumProof" "mc_add1_corr_thm");
val _ = emit "mc_add_corr_thm_typed" (fetch "word_bignumProof" "mc_add_corr_thm");
val _ = emit "mc_add_loop1_corr_thm_typed" (fetch "word_bignumProof" "mc_add_loop1_corr_thm");
val _ = emit "mc_add_loop2_corr_thm_typed" (fetch "word_bignumProof" "mc_add_loop2_corr_thm");
val _ = emit "mc_add_loop_corr_thm_typed" (fetch "word_bignumProof" "mc_add_loop_corr_thm");
val _ = emit "mc_adj_cmp_corr_thm_typed" (fetch "word_bignumProof" "mc_adj_cmp_corr_thm");
val _ = emit "mc_adjust_aux_corr_thm_typed" (fetch "word_bignumProof" "mc_adjust_aux_corr_thm");
val _ = emit "mc_calc_d_corr_thm_typed" (fetch "word_bignumProof" "mc_calc_d_corr_thm");
val _ = emit "mc_cmp2_corr_thm_typed" (fetch "word_bignumProof" "mc_cmp2_corr_thm");
val _ = emit "mc_cmp3_corr_thm_typed" (fetch "word_bignumProof" "mc_cmp3_corr_thm");
val _ = emit "mc_cmp_corr_thm_typed" (fetch "word_bignumProof" "mc_cmp_corr_thm");
val _ = emit "mc_cmp_mul2_corr_thm_typed" (fetch "word_bignumProof" "mc_cmp_mul2_corr_thm");
val _ = emit "mc_compare_corr_thm_typed" (fetch "word_bignumProof" "mc_compare_corr_thm");
val _ = emit "mc_copy_down_corr_thm_typed" (fetch "word_bignumProof" "mc_copy_down_corr_thm");
val _ = emit "mc_copy_over_corr_thm_typed" (fetch "word_bignumProof" "mc_copy_over_corr_thm");
val _ = emit "mc_div0_corr_thm_typed" (fetch "word_bignumProof" "mc_div0_corr_thm");
val _ = emit "mc_div1_corr_thm_typed" (fetch "word_bignumProof" "mc_div1_corr_thm");
val _ = emit "mc_div2_corr_thm_typed" (fetch "word_bignumProof" "mc_div2_corr_thm");
val _ = emit "mc_div3_corr_thm_typed" (fetch "word_bignumProof" "mc_div3_corr_thm");
val _ = emit "mc_div_adjust_corr_thm_typed" (fetch "word_bignumProof" "mc_div_adjust_corr_thm");
val _ = emit "mc_div_corr_thm_typed" (fetch "word_bignumProof" "mc_div_corr_thm");
val _ = emit "mc_div_guess_corr_thm_typed" (fetch "word_bignumProof" "mc_div_guess_corr_thm");
val _ = emit "mc_div_loop_corr_thm_typed" (fetch "word_bignumProof" "mc_div_loop_corr_thm");
val _ = emit "mc_div_r1_corr_thm_typed" (fetch "word_bignumProof" "mc_div_r1_corr_thm");
val _ = emit "mc_div_sub1_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub1_corr_thm");
val _ = emit "mc_div_sub_aux1_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub_aux1_corr_thm");
val _ = emit "mc_div_sub_aux_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub_aux_corr_thm");
val _ = emit "mc_div_sub_call_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub_call_corr_thm");
val _ = emit "mc_div_sub_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub_corr_thm");
val _ = emit "mc_div_sub_loop_corr_thm_typed" (fetch "word_bignumProof" "mc_div_sub_loop_corr_thm");
val _ = emit "mc_div_test_corr_thm_typed" (fetch "word_bignumProof" "mc_div_test_corr_thm");
val _ = emit "mc_fix_corr_thm_typed" (fetch "word_bignumProof" "mc_fix_corr_thm");
val _ = emit "mc_iadd1_corr_thm_typed" (fetch "word_bignumProof" "mc_iadd1_corr_thm");
val _ = emit "mc_iadd2_corr_thm_typed" (fetch "word_bignumProof" "mc_iadd2_corr_thm");
val _ = emit "mc_iadd3_corr_thm_typed" (fetch "word_bignumProof" "mc_iadd3_corr_thm");
val _ = emit "mc_iadd_corr_thm_typed" (fetch "word_bignumProof" "mc_iadd_corr_thm");
val _ = emit "mc_idiv0_corr_thm_typed" (fetch "word_bignumProof" "mc_idiv0_corr_thm");
val _ = emit "mc_idiv_corr_thm_typed" (fetch "word_bignumProof" "mc_idiv_corr_thm");
val _ = emit "mc_idiv_mod_header_corr_thm_typed" (fetch "word_bignumProof" "mc_idiv_mod_header_corr_thm");
val _ = emit "mc_imul1_corr_thm_typed" (fetch "word_bignumProof" "mc_imul1_corr_thm");
val _ = emit "mc_imul_corr_thm_typed" (fetch "word_bignumProof" "mc_imul_corr_thm");
val _ = emit "mc_iop_corr_thm_typed" (fetch "word_bignumProof" "mc_iop_corr_thm");
val _ = emit "mc_isub_flip_corr_thm_typed" (fetch "word_bignumProof" "mc_isub_flip_corr_thm");
val _ = emit "mc_mul_by_single2_corr_thm_typed" (fetch "word_bignumProof" "mc_mul_by_single2_corr_thm");
val _ = emit "mc_mul_by_single_corr_thm_typed" (fetch "word_bignumProof" "mc_mul_by_single_corr_thm");
val _ = emit "mc_mul_corr_thm_typed" (fetch "word_bignumProof" "mc_mul_corr_thm");
val _ = emit "mc_mul_pass_corr_thm_typed" (fetch "word_bignumProof" "mc_mul_pass_corr_thm");
val _ = emit "mc_mul_zero_corr_thm_typed" (fetch "word_bignumProof" "mc_mul_zero_corr_thm");
val _ = emit "mc_simple_div1_corr_thm_typed" (fetch "word_bignumProof" "mc_simple_div1_corr_thm");
val _ = emit "mc_simple_div_corr_thm_typed" (fetch "word_bignumProof" "mc_simple_div_corr_thm");
val _ = emit "mc_single_div_corr_thm_typed" (fetch "word_bignumProof" "mc_single_div_corr_thm");
val _ = emit "mc_single_mul_add_corr_thm_typed" (fetch "word_bignumProof" "mc_single_mul_add_corr_thm");
val _ = emit "mc_single_mul_corr_thm_typed" (fetch "word_bignumProof" "mc_single_mul_corr_thm");
val _ = emit "mc_sub1_corr_thm_typed" (fetch "word_bignumProof" "mc_sub1_corr_thm");
val _ = emit "mc_sub_corr_thm_typed" (fetch "word_bignumProof" "mc_sub_corr_thm");
val _ = emit "mc_sub_loop1_corr_thm_typed" (fetch "word_bignumProof" "mc_sub_loop1_corr_thm");
val _ = emit "mc_sub_loop2_corr_thm_typed" (fetch "word_bignumProof" "mc_sub_loop2_corr_thm");
val _ = emit "mc_sub_loop_corr_thm_typed" (fetch "word_bignumProof" "mc_sub_loop_corr_thm");
val _ = emit "mc_top_two_corr_thm_typed" (fetch "word_bignumProof" "mc_top_two_corr_thm");
val _ = print "word_bignum_corr_probe_end=1\n";
