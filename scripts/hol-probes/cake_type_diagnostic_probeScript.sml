load "infer_tTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val function = rhs (concl (EVAL ``infer_t$inf_type_to_string (Bind [] [])
  (Infer_Tapp [Infer_Tapp [] 5; Infer_Tapp [] 5] 4)``));
val _ = (print "function="; print_term function; print "\n");
val nested = rhs (concl (EVAL ``infer_t$inf_type_to_string (Bind [] [])
  (Infer_Tapp [Infer_Tapp [Infer_Tapp [] 5; Infer_Tapp [] 1] 4] 6)``));
val _ = (print "nested="; print_term nested; print "\n");
val tuple = rhs (concl (EVAL ``infer_t$inf_type_to_string (Bind [] [])
  (Infer_Tapp [Infer_Tapp [] 1; Infer_Tapp [] 5] 9)``));
val _ = (print "tuple="; print_term tuple; print "\n");
val variable = rhs (concl (EVAL ``infer_t$inf_type_to_string (Bind [] []) (Infer_Tuvar 1)``));
val _ = (print "variable="; print_term variable; print "\n");
val named = rhs (concl (EVAL ``infer_t$inf_type_to_string
  (Bind [(«t»,([],Tapp [] 15))] []) (Infer_Tapp [] 15)``));
val _ = (print "named="; print_term named; print "\n");
val qualified = rhs (concl (EVAL ``infer_t$inf_type_to_string
  (Bind [] [(«M», Bind [(«t»,([],Tapp [] 15))] [])]) (Infer_Tapp [] 15)``));
val _ = (print "qualified="; print_term qualified; print "\n");
