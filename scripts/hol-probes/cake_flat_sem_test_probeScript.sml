load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "do_test_typed=" flatSemTheory.do_test_def;
val int_equal = prove(
  ``flatSem$do_test Equal IntT (Litv (IntLit 1)) (Litv (IntLit 1)) = Eq_val T``,
  simp [flatSemTheory.do_test_def, flatSemTheory.check_type_def,
        flatSemTheory.do_eq_def, semanticPrimitivesTheory.lit_same_type_def]);
val _ = if null (hyp int_equal) then print "int_equal=Eq_val T\n" else raise Fail "int_equal";
val _ = show_eval "wrong_int=" ``flatSem$do_test Equal IntT (Litv (IntLit 1)) (Litv (Char #"a"))``;
val _ = show_eval "word64_compare=" ``flatSem$do_test (Compare Lt) (WordT W64) (Litv (Word64 1w)) (Litv (Word64 2w))``;
val _ = show_eval "int_compare=" ``flatSem$do_test (Compare Lt) IntT (Litv (IntLit ~3)) (Litv (IntLit 1))``;
val _ = show_eval "char_compare=" ``flatSem$do_test (Compare Lt) CharT (Litv (Char #"a")) (Litv (Char #"b"))``;
val _ = show_eval "string_compare=" ``flatSem$do_test (Compare Lt) StrT (Litv (StrLit «z»)) (Litv (StrLit «aa»))``;
val _ = show_eval "string_alt_compare=" ``flatSem$do_test (AltCompare Lt) StrT (Litv (StrLit «z»)) (Litv (StrLit «aa»))``;
