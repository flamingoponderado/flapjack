load "flat_patternProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "pmatch_rows_same_FST_typed=";
  Lib.with_flag (Globals.show_types,true)
    print_term (concl flat_patternProofTheory.pmatch_rows_same_FST);
  print "\n");
