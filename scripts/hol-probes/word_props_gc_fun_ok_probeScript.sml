load "preamble"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble wordPropsTheory wordSemTheory wordLangTheory finite_mapTheory;
val _ = Globals.linewidth := 4000;
fun emit label th = (print (label ^ "="); print_thm th; print "\n");
val _ = emit "gc_fun_ok_def" wordPropsTheory.gc_fun_ok_def;
val _ = print "gc_fun_ok_hypotheses=";
val _ = print (Int.toString (length (hyp wordPropsTheory.gc_fun_ok_def)) ^ "\n");
val guarded_handler = prove(
  ``!s:store_name |-> 'a word_loc.
      Handler IN FDOM s ==> FLOOKUP s Handler = SOME (s ' Handler)``,
  simp [FLOOKUP_DEF]);
val _ = emit "guarded_handler_lookup" guarded_handler;
val always_fail = prove(
  ``gc_fun_ok (\(wl:'a word_loc list,m,d,s). NONE)``,
  simp [gc_fun_ok_def]);
val _ = emit "always_fail_gc" always_fail;
val _ = print "\n";
