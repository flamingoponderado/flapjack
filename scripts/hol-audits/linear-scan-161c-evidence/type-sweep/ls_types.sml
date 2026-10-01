load "bossLib"; load "linear_scanTheory"; open HolKernel Parse boolLib bossLib linear_scanTheory;
val _ = Globals.linewidth := 1000;
val _ = List.app (fn c => let val (n,ty) = dest_const c in print (n ^ "="); print_type ty; print "\n" end) (constants "linear_scan");
