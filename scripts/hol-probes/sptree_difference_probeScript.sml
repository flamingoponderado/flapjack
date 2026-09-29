(*
  Direct HOL-EVAL rows for every clause of sptree$difference
  (HOL/src/finite_maps/sptreeScript.sml:319-339).  Inputs are constructed
  directly so each LN/LS/BN/BS case and the mk_BN/mk_BS collapses are visible.
  The right tree uses bool while the left uses num to pin the heterogeneous
  value type of difference.
*)
load "bossLib";
load "sptreeTheory";
open bossLib;
open HolKernel Parse;
open sptreeTheory;

fun pe label q =
  let val th = EVAL q
  in print (label ^ "="); print_term (snd (boolSyntax.dest_eq (concl th))); print "\n" end;

pe "difference_ln_bs" ``difference (LN:num spt) (BS LN T LN)``;
pe "difference_ls_ln" ``difference (LS (17:num)) (LN:bool spt)``;
pe "difference_ls_ls" ``difference (LS (17:num)) (LS F)``;
pe "difference_ls_bn" ``difference (LS (17:num)) (BN (LS T) LN)``;
pe "difference_ls_bs" ``difference (LS (17:num)) (BS LN F LN)``;
pe "difference_bn_ln" ``difference (BN (LS (11:num)) (LS 22)) (LN:bool spt)``;
pe "difference_bn_ls" ``difference (BN (LS (11:num)) (LS 22)) (LS F)``;
pe "difference_bn_bn" ``difference (BN (LS (11:num)) (LS 22)) (BN (LS T) LN)``;
pe "difference_bn_collapse" ``difference (BN (LS (11:num)) LN) (BN (LS T) LN)``;
pe "difference_bn_bs" ``difference (BN (LS (11:num)) (LS 22)) (BS (LS T) F LN)``;
pe "difference_bs_ln" ``difference (BS (LS (11:num)) 33 (LS 22)) (LN:bool spt)``;
pe "difference_bs_ls" ``difference (BS (LS (11:num)) 33 (LS 22)) (LS F)``;
pe "difference_bs_bn_collapse" ``difference (BS LN (33:num) LN) (BN LN LN)``;
pe "difference_bs_bn" ``difference (BS (LS (11:num)) 33 (LS 22)) (BN (LS T) LN)``;
pe "difference_bs_bs" ``difference (BS (LS (11:num)) 33 (LS 22)) (BS LN F LN)``;
pe "difference_bs_bs_collapse" ``difference (BS (LS (11:num)) 33 LN) (BS (LS T) F LN)``;
