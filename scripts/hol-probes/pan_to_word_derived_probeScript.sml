load "bossLib";
load "preamble";
open bossLib HolKernel Parse preamble listTheory;
val _ = show_types := true;
val th = ALL_DISTINCT_MAP_INJ
  |> Q.SPEC `MAP FST (xs : ('a # 'e) list)`
  |> SIMP_RULE std_ss [MAP_MAP_o, o_DEF];
val _ = (print "ALL_DISTINCT_MAP_INJ_o="; print_term (concl th); print "\n");
