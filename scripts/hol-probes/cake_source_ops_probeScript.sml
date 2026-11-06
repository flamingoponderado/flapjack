load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "eq_type="; print_type (type_of ``semanticPrimitives$do_eq``); print "\n");
val _ = (print "apply_type="; print_type (type_of ``semanticPrimitives$do_opapp``); print "\n");
val literal_equal = rhs (concl (EVAL ``semanticPrimitives$do_eq (Litv (IntLit 3)) (Litv (IntLit 3))``));
val _ = (print "literal_equal="; print_term literal_equal; print "\n");
val literal_type = rhs (concl (EVAL ``semanticPrimitives$do_eq (Litv (IntLit 3)) (Litv (Char #"a"))``));
val _ = (print "literal_type="; print_term literal_type; print "\n");
val eq_short_circuit = rhs (concl (EVAL ``semanticPrimitives$do_eq_list
  [Litv (IntLit 1); Litv (IntLit 1)] [Litv (IntLit 2); Litv (Char #"a")]``));
val _ = (print "eq_short_circuit="; print_term eq_short_circuit; print "\n");
val ref_type = rhs (concl (EVAL ``semanticPrimitives$do_eq (Loc F 1) (Loc T 1)``));
val _ = (print "ref_type="; print_term ref_type; print "\n");
val different_constructor = rhs (concl (EVAL ``semanticPrimitives$do_eq
  (Conv (SOME (TypeStamp «A» 7)) []) (Conv (SOME (TypeStamp «B» 7)) [])``));
val _ = (print "different_constructor="; print_term different_constructor; print "\n");
val function_equal = rhs (concl (EVAL ``semanticPrimitives$do_eq
  (Closure <| v := Bind [] []; c := Bind [] [] |> «x» (Var (Short «x»)))
  (Recclosure <| v := Bind [] []; c := Bind [] [] |> [] «f»)``));
val _ = (print "function_equal="; print_term function_equal; print "\n");
val application = rhs (concl (EVAL ``case semanticPrimitives$do_opapp
  [Closure <| v := Bind [] []; c := Bind [] [] |> «x» (Var (Short «x»)); Litv (IntLit 4)] of
    NONE => NONE | SOME (env, _) => nsLookup env.v (Short «x»)``));
val _ = (print "application="; print_term application; print "\n");
val duplicate = rhs (concl (EVAL ``semanticPrimitives$do_opapp
  [Recclosure <| v := Bind [] []; c := Bind [] [] |>
    [(«f»,«x»,Var (Short «x»)); («f»,«y»,Var (Short «y»))] «f»; Litv (IntLit 4)]``));
val _ = (print "duplicate="; print_term duplicate; print "\n");
