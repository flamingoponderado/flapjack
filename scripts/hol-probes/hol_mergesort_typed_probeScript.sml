(* Typed statements of the HOL `mergesort` theory declarations ported in
   `Flapjack/Misc/Mergesort*.lean`, from the built HOL4 core theory (no rebuild). *)
load "mergesortTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_parse label t =
  (print label; Lib.with_flag (Globals.show_types,true) print_term t; print "\n");
val _ = show_parse "mem_sorted_append_typed="
  ``!R:'a -> 'a -> bool. !l1 l2:'a list. !x y:'a.
      transitive R /\ SORTED R (l1 ++ l2) /\ MEM x l1 /\ MEM y l2 ==> R x y``;
val _ = show_thm "merge_def_typed=" mergesortTheory.merge_def;
val _ = show_thm "merge_empty_typed=" mergesortTheory.merge_empty;
val _ = show_parse "merge_last_lem1_typed="
  ``!R:'a -> 'a -> bool. !l1 l2:'a list. !x:'a.
      (!y:'a. MEM y l2 ==> ~R x y) ==>
      merge R (l1 ++ [x]) l2 = merge R l1 l2 ++ [x]``;
val _ = show_parse "merge_last_lem2_typed="
  ``!R:'a -> 'a -> bool. !l1 l2:'a list. !y:'a.
      (!x:'a. MEM x l1 ==> R x y) ==>
      merge R l1 (l2 ++ [y]) = merge R l1 l2 ++ [y]``;
val _ = show_thm "merge_sorted_typed=" mergesortTheory.merge_sorted;
val _ = show_thm "merge_tail_correct1_typed=" mergesortTheory.merge_tail_correct1;
val _ = show_thm "merge_tail_correct2_typed=" mergesortTheory.merge_tail_correct2;
val _ = show_thm "mergesortN_def_typed=" mergesortTheory.mergesortN_def;
val _ = show_thm "mergesortN_correct_typed=" mergesortTheory.mergesortN_correct;
val _ = show_thm "mergesortN_sorted_typed=" mergesortTheory.mergesortN_sorted;
val _ = show_thm "sort2_def_typed=" mergesortTheory.sort2_def;
val _ = show_thm "sort2_sorted_typed=" mergesortTheory.sort2_sorted;
val _ = show_thm "sort2_tail_correct_typed=" mergesortTheory.sort2_tail_correct;
val _ = show_thm "sort3_def_typed=" mergesortTheory.sort3_def;
val _ = show_thm "sort3_sorted_typed=" mergesortTheory.sort3_sorted;
val _ = show_thm "sort3_tail_correct_typed=" mergesortTheory.sort3_tail_correct;
