(* Original word_alloc option_lookup, priority, fake_move, fake_moves and
   fix_inconsistencies at 64-bit words. CakeML remains read-only; sparse trees
   print raw. *)
load "bossLib";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib word_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val _ = observe "ol_hit" ``option_lookup (insert 3 9 LN) 3``;
val _ = observe "ol_miss" ``option_lookup (insert 3 9 LN) 4``;
val _ = observe "pr_none" ``(priority NONE T, priority NONE F)``;
val _ = observe "pr_inl" ``(priority (SOME (INL ())) T, priority (SOME (INL ())) F)``;
val _ = observe "pr_inr" ``(priority (SOME (INR ())) T, priority (SOME (INR ())) F)``;
val _ = observe "fm" ``fake_move 7 : 64 wordLang$prog``;
val _ = observe "fms_empty" ``fake_moves NONE [] (insert 1 5 LN) LN 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map # num num_map``;
val _ = observe "fms_left_only" ``fake_moves (SOME (INL ())) [1] (insert 1 5 LN) LN 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map # num num_map``;
val _ = observe "fms_right_only" ``fake_moves (SOME (INR ())) [2] LN (insert 2 6 LN) 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map # num num_map``;
val _ = observe "fms_both" ``fake_moves NONE [1;2;3] (insert 1 5 (insert 3 7 LN)) (insert 2 6 (insert 3 8 LN)) 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map # num num_map``;
val _ = observe "fi_equal" ``fix_inconsistencies NONE (insert 1 5 LN) (insert 1 5 LN) 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map``;
val _ = observe "fi_mixed" ``fix_inconsistencies (SOME (INL ())) (insert 1 5 (insert 3 7 LN)) (insert 2 6 (insert 3 8 LN)) 13 : 64 wordLang$prog # 64 wordLang$prog # num # num num_map``;
