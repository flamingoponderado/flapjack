(* Capture the generated mini-program that feeds the pinned bignum compiler. *)
load "word_bignumTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "mini_type="; print_type (type_of ``word_bignum$mc_iop_code``); print "\n");
val generic = rhs (concl (EVAL ``word_bignum$mc_iop_code : 'a word_bignum$mini``));
val _ = (print "generic="; print_term generic; print "\n");
val result = rhs (concl (EVAL ``word_bignum$mc_iop_code : 64 word_bignum$mini``));
val _ = (print "mini="; print_term result; print "\n");
val _ = show_types := true;
val _ = if null (hyp word_bignumTheory.mc_iop_code_def) then
  (print "mc_iop_code_def_typed="; print_term (concl word_bignumTheory.mc_iop_code_def); print "\n")
  else raise Fail "mc_iop_code_def has unexpected hypotheses";
val _ = if null (hyp word_bignumTheory.all_code_defs) then
  (print "all_code_defs_typed="; print_term (concl word_bignumTheory.all_code_defs); print "\n")
  else raise Fail "all_code_defs has unexpected hypotheses";
val _ = if null (hyp word_bignumTheory.generated_bignum_stubs_def) then
  (print "generated_bignum_stubs_def_typed="; print_term (concl word_bignumTheory.generated_bignum_stubs_def); print "\n")
  else raise Fail "generated_bignum_stubs_def has unexpected hypotheses";
