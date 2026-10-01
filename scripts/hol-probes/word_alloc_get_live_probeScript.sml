(* Direct original full program-liveness observations. CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "get_live_store_consts"
  ``let live = sptree$fromAList [(1n,());(2n,());(9n,())] in
    let out = get_live (StoreConsts 1 2 3 4 [] : 8 wordLang$prog) live [] in
    sptree$lookup 1 out = NONE /\ sptree$lookup 2 out = NONE /\
    sptree$lookup 3 out = SOME () /\ sptree$lookup 4 out = SOME () /\
    sptree$lookup 9 out = SOME ()``;
val _ = print_eval "get_live_break_outside"
  ``get_live (Break 2 : 8 wordLang$prog) sptree$LN [] = sptree$LN``;
val _ = print_eval "get_live_return"
  ``let out = get_live (Return 1 [2;2] : 8 wordLang$prog) sptree$LN [] in
    sptree$lookup 1 out = SOME () /\ sptree$lookup 2 out = SOME () /\
    sptree$lookup 3 out = NONE``;
