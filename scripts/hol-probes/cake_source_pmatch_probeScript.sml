load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "pmatch_type="; print_type (type_of ``semanticPrimitives$pmatch``); print "\n");
val variable = rhs (concl (EVAL ``semanticPrimitives$pmatch (Bind [] []) []
  (Pvar «x») (Litv (IntLit 4)) []``));
val _ = (print "variable="; print_term variable; print "\n");
val no_match = rhs (concl (EVAL ``semanticPrimitives$pmatch
  (Bind [(«A»,(0,TypeStamp «A» 7))] []) []
  (Pcon (SOME (Short «A»)) []) (Conv (SOME (TypeStamp «B» 7)) []) []``));
val _ = (print "no_match="; print_term no_match; print "\n");
val wrong_arity = rhs (concl (EVAL ``semanticPrimitives$pmatch
  (Bind [(«A»,(1,TypeStamp «A» 7))] []) []
  (Pcon (SOME (Short «A»)) []) (Conv (SOME (TypeStamp «B» 7)) []) []``));
val _ = (print "wrong_arity="; print_term wrong_arity; print "\n");
val later_type_error = rhs (concl (EVAL ``semanticPrimitives$pmatch_list (Bind [] []) []
  [Plit (IntLit 1); Plit (IntLit 0)] [Litv (IntLit 2); Litv (Char #"a")] []``));
val _ = (print "later_type_error="; print_term later_type_error; print "\n");
val reference = rhs (concl (EVAL ``semanticPrimitives$pmatch (Bind [] []) [Refv (Litv (IntLit 4))]
  (Pref (Pvar «x»)) (Loc T 0) []``));
val _ = (print "reference="; print_term reference; print "\n");
val invalid_ref = rhs (concl (EVAL ``semanticPrimitives$pmatch (Bind [] []) []
  (Pref (Pvar «x»)) (Loc T 0) []``));
val _ = (print "invalid_ref="; print_term invalid_ref; print "\n");
val safe_no_match = rhs (concl (EVAL ``semanticPrimitives$can_pmatch_all (Bind [] []) []
  [Plit (IntLit 1)] (Litv (IntLit 2))``));
val _ = (print "safe_no_match="; print_term safe_no_match; print "\n");
val unsafe_match = rhs (concl (EVAL ``semanticPrimitives$can_pmatch_all (Bind [] []) []
  [Plit (IntLit 1)] (Litv (Char #"a"))``));
val _ = (print "unsafe_match="; print_term unsafe_match; print "\n");
