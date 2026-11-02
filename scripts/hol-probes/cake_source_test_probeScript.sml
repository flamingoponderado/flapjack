load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "do_eq_definition=" semanticPrimitivesTheory.do_eq_def;
val _ = show_thm "check_type_definition=" semanticPrimitivesTheory.check_type_def;
val _ = show_thm "dest_lit_definition=" semanticPrimitivesTheory.dest_Litv_def;
val _ = show_thm "num_cmp_definition=" semanticPrimitivesTheory.num_cmp_def;
val _ = show_thm "int_cmp_definition=" semanticPrimitivesTheory.int_cmp_def;
val _ = show_thm "shift8_definition=" semanticPrimitivesTheory.shift8_lookup_def;
val _ = show_thm "shift64_definition=" semanticPrimitivesTheory.shift64_lookup_def;
val _ = show_thm "do_test_definition=" semanticPrimitivesTheory.do_test_def;
val _ = (print "eq_val_type="; print_type (type_of ``semanticPrimitives$Eq_val``); print "\n");
val _ = (print "type="; print_type (type_of ``semanticPrimitives$do_test``); print "\n");
val int_eq = rhs (concl ((SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_test_def,
  semanticPrimitivesTheory.check_type_def, semanticPrimitivesTheory.do_eq_def,
  semanticPrimitivesTheory.lit_same_type_def])
  ``semanticPrimitives$do_test Equal IntT (Litv (IntLit 1)) (Litv (IntLit 1))``));
val _ = (print "int_eq="; print_term int_eq; print "\n");
val mismatch = rhs (concl ((SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_test_def,
  semanticPrimitivesTheory.check_type_def])
  ``semanticPrimitives$do_test Equal IntT (Litv (IntLit 1)) (Litv (Char #"a"))``));
val _ = (print "mismatch="; print_term mismatch; print "\n");
val word64 = rhs (concl (EVAL ``semanticPrimitives$do_test (Compare Lt) (WordT W64)
  (Litv (Word64 (1w:word64))) (Litv (Word64 (2w:word64)))``));
val _ = (print "word64="; print_term word64; print "\n");
val int_compare = rhs (concl (EVAL ``semanticPrimitives$do_test (Compare Lt) IntT
  (Litv (IntLit (-3))) (Litv (IntLit 1))``));
val _ = (print "int_compare="; print_term int_compare; print "\n");
val str_normal = rhs (concl (EVAL ``semanticPrimitives$do_test (Compare Lt) StrT
  (Litv (StrLit «z»)) (Litv (StrLit «aa»))``));
val _ = (print "str_normal="; print_term str_normal; print "\n");
val str_fast = rhs (concl (EVAL ``semanticPrimitives$do_test (AltCompare Lt) StrT
  (Litv (StrLit «z»)) (Litv (StrLit «aa»))``));
val _ = (print "str_fast="; print_term str_fast; print "\n");
