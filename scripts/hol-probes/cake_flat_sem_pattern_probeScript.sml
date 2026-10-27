load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "stamp_rules_typed=" flatSemTheory.pmatch_stamps_ok_rules;
val _ = show_thm "stamp_cases_typed=" flatSemTheory.pmatch_stamps_ok_cases;
val _ = show_thm "pmatch_typed=" flatSemTheory.pmatch_def;
val _ = show_thm "rows_typed=" flatSemTheory.pmatch_rows_def;
val _ = show_eval "wildcard=" ``flatSem$pmatch (ARB : (unit, unit) flatSem$state) flatLang$Pany (Litv (IntLit 1)) []``;
val _ = show_eval "literal_same=" ``flatSem$pmatch (ARB : (unit, unit) flatSem$state) (flatLang$Plit (IntLit 1)) (Litv (IntLit 1)) []``;
val _ = show_eval "literal_mismatch=" ``flatSem$pmatch (ARB : (unit, unit) flatSem$state) (flatLang$Plit (IntLit 1)) (Litv (IntLit 2)) []``;
val _ = show_eval "literal_wrong_type=" ``flatSem$pmatch (ARB : (unit, unit) flatSem$state) (flatLang$Plit (IntLit 1)) (Litv (Char #"a")) []``;
val tuple_length = prove(
  ``flatSem$pmatch (ARB : (unit, unit) flatSem$state) (flatLang$Pcon NONE [])
    (Conv NONE [Litv (IntLit 1)]) [] = Match_type_error``,
  simp [flatSemTheory.pmatch_def, Once flatSemTheory.pmatch_stamps_ok_cases]);
val _ = if null (hyp tuple_length) then print "tuple_length=Match_type_error\n" else raise Fail "tuple_length";
val different_constructor = prove(
  ``flatSem$pmatch (ARB : (unit, unit) flatSem$state)
      (flatLang$Pcon (SOME (0, SOME (1, [(0,0); (1,0)]))) [])
      (Conv (SOME (1, SOME 1)) []) [] = No_match``,
  simp [flatSemTheory.pmatch_def, Once flatSemTheory.pmatch_stamps_ok_cases]);
val _ = if null (hyp different_constructor) then print "different_constructor=No_match\n" else raise Fail "different_constructor";
val wrong_constructor_type = prove(
  ``flatSem$pmatch (ARB : (unit, unit) flatSem$state)
      (flatLang$Pcon (SOME (0, SOME (1, [(0,0)]))) [])
      (Conv (SOME (0, SOME 2)) []) [] = Match_type_error``,
  simp [flatSemTheory.pmatch_def, Once flatSemTheory.pmatch_stamps_ok_cases]);
val _ = if null (hyp wrong_constructor_type) then print "wrong_constructor_type=Match_type_error\n" else raise Fail "wrong_constructor_type";
val _ = show_eval "list_error_precedence=" ``flatSem$pmatch_list (ARB : (unit, unit) flatSem$state) [flatLang$Plit (IntLit 1); flatLang$Plit (IntLit 0)] [Litv (IntLit 2); Litv (Char #"a")] []``;
