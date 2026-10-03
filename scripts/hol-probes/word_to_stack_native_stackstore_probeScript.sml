load "preamble"; load "word_to_stackTheory";
open HolKernel Parse bossLib preamble word_to_stackTheory;
val _ = Globals.linewidth := 1000000;
fun row label th = (print(label ^ "="); print_thm th; print "\n");
val _ = row "native_stackstore_full_definition" wStackStore_def;
val _ = row "native_stackstore_empty" (EVAL ``wStackStore [] Skip : 64 stackLang$prog``);
val _ = row "native_stackstore_reverse" (EVAL ``wStackStore [(3,4);(5,6)] Skip : 64 stackLang$prog``);
val _ = row "native_stackstore_repeated_slot" (EVAL ``wStackStore [(3,4);(5,4)] (Tick : 64 stackLang$prog)``);
