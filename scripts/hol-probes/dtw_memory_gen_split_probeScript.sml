load "data_to_word_memoryProofTheory";
open HolKernel Parse boolLib bossLib;
val st = Term `!cc roots heap roots1 s.
  (gen_gc cc (roots,heap) = (roots1,s)) /\
  (!t r. (cc.isRef (t,r) <=> isMutTag t)) ==>
  (EVERY (\x. ~isRef x)) (s.h1 ++ s.h2) /\
  EVERY isDataElement (s.h1 ++ s.h2) /\
  EVERY isRef (s.r1 ++ s.r2 ++ s.r3 ++ s.r4)`;
val _ = (print "gen_gc_data_refs_split="; print_term st; print "\n");
val _ = (print "gen_gc_type="; print (type_to_string (type_of ``gen_gc``)); print "\n");
val _ = (print "isRef_type="; print (type_to_string (type_of ``isRef``)); print "\n");
val _ = (print "isDataElement_type="; print (type_to_string (type_of ``isDataElement``)); print "\n");
