(* Capture the generated mini-program that feeds the pinned bignum compiler. *)
load "word_bignumTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "mini_type="; print_type (type_of ``word_bignum$mc_iop_code``); print "\n");
val generic = rhs (concl (EVAL ``word_bignum$mc_iop_code : 'a word_bignum$mini``));
val _ = (print "generic="; print_term generic; print "\n");
val result = rhs (concl (EVAL ``word_bignum$mc_iop_code : 64 word_bignum$mini``));
val _ = (print "mini="; print_term result; print "\n");
