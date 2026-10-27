load "inferTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val first = rhs (concl (EVAL ``infer$find_dup [«A»; «B»; «A»; «B»]``));
val _ = (print "first="; print_term first; print "\n");
val constructor = rhs (concl (EVAL ``infer$check_type_definition
  <| loc := SOME (Locs (POSN 0 0) (POSN 0 19)); err := Bind [] [] |>
  (Bind [] []) [([], «t», [(«A», []); («A», [])])]
  <| next_uvar := 0; subst := FEMPTY; next_id := 15 |>``));
val _ = (print "constructor="; print_term constructor; print "\n");
