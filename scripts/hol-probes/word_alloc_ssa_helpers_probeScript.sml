(* Original word_alloc list_next_var_rename_move, force_rename, mk_prio,
   ssa_reconcile and loop_setup at 64-bit words. CakeML remains read-only;
   sparse trees print raw. *)
load "bossLib";
load "wordsLib";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib word_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val m = ``insert 2 10 (insert 3 11 (insert 4 12 LN)) : num num_map``;
val _ = observe "lnvrm_basic" ``list_next_var_rename_move ^m 21 [3;9;2] : 64 wordLang$prog # num num_map # num``;
val _ = observe "lnvrm_empty" ``list_next_var_rename_move ^m 21 [] : 64 wordLang$prog # num num_map # num``;
val _ = observe "fr_basic" ``force_rename [(2,30);(7,31);(2,32)] ^m``;
val _ = observe "mp_left" ``mk_prio (Skip : 64 wordLang$prog) (Tick : 64 wordLang$prog)``;
val _ = observe "mp_right" ``mk_prio (Tick : 64 wordLang$prog) (Skip : 64 wordLang$prog)``;
val _ = observe "mp_both" ``mk_prio (Skip : 64 wordLang$prog) (Skip : 64 wordLang$prog)``;
val _ = observe "mp_none" ``mk_prio (Tick : 64 wordLang$prog) (Raise 2 : 64 wordLang$prog)``;
val _ = observe "sr_moves" ``ssa_reconcile ^m (insert 2 40 (insert 3 11 LN)) (insert 2 () (insert 3 () (insert 9 () LN))) : 64 wordLang$prog``;
val _ = observe "sr_skip" ``ssa_reconcile ^m ^m (insert 2 () (insert 3 () LN)) : 64 wordLang$prog``;
val _ = observe "sr_payload" ``ssa_reconcile ^m (insert 4 50 LN) (insert 4 T LN) : 64 wordLang$prog``;
val _ = observe "ls_mixed" ``loop_setup (insert 2 () (insert 9 () LN)) (insert 4 () (insert 7 () LN)) ^m 21 : 64 wordLang$prog # num num_map # num``;
val _ = observe "ls_empty" ``loop_setup LN LN ^m 21 : 64 wordLang$prog # num num_map # num``;
