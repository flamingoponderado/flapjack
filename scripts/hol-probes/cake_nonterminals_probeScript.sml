load "gramTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = (print "constructors=";
  print (String.concatWith "," (map term_to_string (TypeBase.constructors_of ``:MMLnonT``)));
  print "\n");
