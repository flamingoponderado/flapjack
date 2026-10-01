(* Direct original program-write observations. CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "writes_move"
  ``get_writes (Move 5 [(1,9);(1,8);(2,7)]:8 wordLang$prog) =
    sptree$insert 1 () (sptree$insert 1 () (sptree$insert 2 () sptree$LN))``;
val _ = print_eval "writes_store_consts"
  ``get_writes (StoreConsts 1 2 3 4 []:8 wordLang$prog) =
    sptree$insert 1 () (sptree$insert 2 () (sptree$insert 3 () (sptree$insert 4 () sptree$LN)))``;
val _ = print_eval "writes_inst_load16"
  ``get_writes (Inst (Mem Load16 1 (Addr 2 0w)):8 wordLang$prog) = sptree$LN``;
val _ = print_eval "writes_shared_load16"
  ``get_writes (ShareInst Load16 1 (Var 2):8 wordLang$prog) = sptree$insert 1 () sptree$LN``;
val _ = print_eval "writes_shared_store16"
  ``get_writes (ShareInst Store16 1 (Var 2):8 wordLang$prog) = sptree$LN``;
val _ = print_eval "writes_seq_catchall"
  ``get_writes (Seq (LocValue 1 2) (LocValue 3 4):8 wordLang$prog) = sptree$LN``;
val _ = print_eval "writes_install"
  ``get_writes (Install 1 2 3 4 (sptree$LN,sptree$LN):8 wordLang$prog) =
    sptree$insert 1 () sptree$LN``;
