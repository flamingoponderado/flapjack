load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm =
  (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "do_eq_typed=" flatSemTheory.do_eq_def;
val _ = show_thm "do_opapp_typed=" flatSemTheory.do_opapp_def;
val _ = show_eval "literal_equal=" ``flatSem$do_eq (Litv (IntLit 4)) (Litv (IntLit 4))``;
val _ = show_eval "literal_mismatch=" ``flatSem$do_eq (Litv (IntLit 4)) (Litv (Char #"a"))``;
val _ = show_eval "location_equal=" ``flatSem$do_eq (Loc T 3) (Loc T 3)``;
val _ = show_eval "location_rejected=" ``flatSem$do_eq (Loc F 3) (Loc T 3)``;
val _ = show_eval "constructor_same_type=" ``flatSem$do_eq (Conv (SOME (0, SOME 1)) []) (Conv (SOME (2, SOME 1)) [])``;
val _ = show_eval "constructor_wrong_type=" ``flatSem$do_eq (Conv (SOME (0, SOME 1)) []) (Conv (SOME (0, SOME 2)) [])``;
val _ = show_eval "vector_different_lengths=" ``flatSem$do_eq (Vectorv []) (Vectorv [Litv (IntLit 1)])``;
val _ = show_eval "list_mismatch=" ``flatSem$do_eq_list [Litv (IntLit 1)] []``;
val _ = show_eval "closure_application=" ``flatSem$do_opapp [Closure <| v := [] |> «x» (flatLang$Lit backend_common$None (IntLit 9)); Litv (IntLit 4)]``;
val _ = show_eval "recursive_duplicate=" ``flatSem$do_opapp [Recclosure <| v := [] |> [(«f»,«x»,flatLang$Lit backend_common$None (IntLit 9)); («f»,«y»,flatLang$Lit backend_common$None (IntLit 8))] «f»; Litv (IntLit 4)]``;
