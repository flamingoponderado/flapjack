load "primTypesTheory";
open HolKernel Parse boolLib bossLib primTypesTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (prim_types_program_def)) then () else raise Fail "hypotheses: prim_types_program_def";
val _ = (print "prim_types_program_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (prim_types_program_def)); print "\n");
