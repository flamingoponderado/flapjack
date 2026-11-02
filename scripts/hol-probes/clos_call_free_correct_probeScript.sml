load "closPropsTheory"; load "clos_callTheory"; load "clos_callProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "free_thm="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.free_thm); print "\n");
val _ = (print "closed_fn_fv="; Lib.with_flag (Globals.show_types,true) print_term (concl clos_callProofTheory.closed_Fn_fv); print "\n");
val closed_cases = EVAL ``(clos_call$closed (closLang$Fn «f» (SOME 4) NONE 2 (closLang$Var None 1)), clos_call$closed (closLang$Fn «f» (SOME 4) NONE 2 (closLang$Var None 2)), clos_call$closed (closLang$Fn «f» (SOME 4) NONE 1 (closLang$Let None [closLang$Var None 0] (closLang$Var None 1))), clos_call$closed (closLang$Fn «f» (SOME 4) NONE 1 (closLang$Let None [closLang$Var None 0] (closLang$Var None 2))))``;
val _ = (print "closed_cases="; print_term (rhs (concl closed_cases)); print "\n");
