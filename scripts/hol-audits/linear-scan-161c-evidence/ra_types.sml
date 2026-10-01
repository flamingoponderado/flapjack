load "bossLib"; load "reg_allocTheory"; open HolKernel Parse boolLib bossLib reg_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = List.app (fn c => let val (n,ty) = dest_const c in print (n ^ "="); print_type ty; print "\n" end) (constants "reg_alloc");
