load "flat_patternProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "pmatch_rows_same_FST_typed=";
  Lib.with_flag (Globals.show_types,true)
    print_term (concl flat_patternProofTheory.pmatch_rows_same_FST);
  print "\n");
val _ = if null (hyp flat_patternProofTheory.max_dec_name_LESS_EVERY) then () else
  raise Fail "hypotheses: max_dec_name_LESS_EVERY";
val _ = (print "max_dec_name_LESS_EVERY_typed=";
  Lib.with_flag (Globals.show_types,true)
    print_term (concl flat_patternProofTheory.max_dec_name_LESS_EVERY);
  print "\n");
val _ = if null (hyp flat_patternProofTheory.FLOOKUP_encode_refs) then () else
  raise Fail "hypotheses: FLOOKUP_encode_refs";
val _ = (print "FLOOKUP_encode_refs_typed=";
  Lib.with_flag (Globals.show_types,true)
    print_term (concl flat_patternProofTheory.FLOOKUP_encode_refs);
  print "\n");
