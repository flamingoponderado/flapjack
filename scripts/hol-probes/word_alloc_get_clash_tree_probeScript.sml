(* Direct original full-program clash-tree observations. CakeML remains
   read-only. Every row is a boolean full-tree equality over the exact
   wordLang program carrier; num_set operands are explicit spt trees so the
   expected trees reduce with the same sptree$union/insert operations. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "gct_skip"
  ``get_clash_tree (Skip : 8 wordLang$prog) [] = Delta [] []``;
val _ = print_eval "gct_move"
  ``get_clash_tree (Move 3 [(1n,2n);(3n,4n)] : 8 wordLang$prog) [] =
    Delta [1;3] [2;4]``;
val _ = print_eval "gct_inst"
  ``get_clash_tree (Inst (Arith (Binop Add 1 2 (Reg 3))) : 8 wordLang$prog) [] =
    Delta [1] [2;3]``;
val _ = print_eval "gct_assign"
  ``get_clash_tree (Assign 1 (Op Add [Var 2; Var 3]) : 8 wordLang$prog) [] =
    Delta [1] [2;3]``;
val _ = print_eval "gct_get"
  ``get_clash_tree (Get 1 NextFree : 8 wordLang$prog) [] = Delta [1] []``;
val _ = print_eval "gct_store"
  ``get_clash_tree (Store (Var 2) 3 : 8 wordLang$prog) [] = Delta [] [3;2]``;
val _ = print_eval "gct_seq"
  ``get_clash_tree (Seq Skip Tick : 8 wordLang$prog) [] =
    Seq (Delta [] []) (Delta [] [])``;
val _ = print_eval "gct_if_reg"
  ``get_clash_tree (If Equal 1 (Reg 2) Skip Tick : 8 wordLang$prog) [] =
    Seq (Delta [] [1;2]) (Branch NONE (Delta [] []) (Delta [] []))``;
val _ = print_eval "gct_if_imm"
  ``get_clash_tree (If Equal 1 (Imm (7w:8 word)) Skip Tick : 8 wordLang$prog) [] =
    Seq (Delta [] [1]) (Branch NONE (Delta [] []) (Delta [] []))``;
val _ = print_eval "gct_mustterminate"
  ``get_clash_tree (MustTerminate Skip : 8 wordLang$prog) [] = Delta [] []``;
val _ = print_eval "gct_alloc"
  ``let a = sptree$fromAList [(1n,());(2n,())] in
    let b = sptree$fromAList [(3n,());(4n,())] in
    get_clash_tree (Alloc 5 (a,b) : 8 wordLang$prog) [] =
      Seq (Delta [] [5]) (Set (sptree$union a b))``;
val _ = print_eval "gct_install"
  ``let a = sptree$fromAList [(1n,());(2n,())] in
    let b = sptree$fromAList [(3n,());(4n,())] in
    get_clash_tree (Install 1 2 3 4 (a,b) : 8 wordLang$prog) [] =
      Seq (Delta [] [4;3;2;1])
        (Seq (Set (sptree$union a b)) (Delta [1] []))``;
val _ = print_eval "gct_codebufferwrite"
  ``get_clash_tree (CodeBufferWrite 1 2 : 8 wordLang$prog) [] = Delta [] [2;1]``;
val _ = print_eval "gct_databufferwrite"
  ``get_clash_tree (DataBufferWrite 1 2 : 8 wordLang$prog) [] = Delta [] [2;1]``;
val _ = print_eval "gct_ffi"
  ``let a = sptree$fromAList [(1n,());(2n,())] in
    let b = sptree$fromAList [(3n,());(4n,())] in
    get_clash_tree (FFI (strlit [CHR 65]) 1 2 3 4 (a,b) : 8 wordLang$prog) [] =
      Seq (Delta [] [1;2;3;4]) (Set (sptree$union a b))``;
val _ = print_eval "gct_raise"
  ``get_clash_tree (Raise 1 : 8 wordLang$prog) [] = Delta [] [1]``;
val _ = print_eval "gct_return"
  ``get_clash_tree (Return 1 [2;3] : 8 wordLang$prog) [] = Delta [] [1;2;3]``;
val _ = print_eval "gct_tick"
  ``get_clash_tree (Tick : 8 wordLang$prog) [] = Delta [] []``;
val _ = print_eval "gct_locvalue"
  ``get_clash_tree (LocValue 1 2 : 8 wordLang$prog) [] = Delta [1] []``;
val _ = print_eval "gct_set"
  ``get_clash_tree (Set NextFree (Var 2) : 8 wordLang$prog) [] = Delta [] [2]``;
val _ = print_eval "gct_opcurrheap"
  ``get_clash_tree (OpCurrHeap Add 1 2 : 8 wordLang$prog) [] = Delta [1] [2]``;
val _ = print_eval "gct_storeconsts"
  ``get_clash_tree (StoreConsts 1 2 3 4 [] : 8 wordLang$prog) [] =
    Delta [1;2;3;4] [3;4]``;
val _ = print_eval "gct_shareinst_store"
  ``get_clash_tree (ShareInst Store 5 (Var 2) : 8 wordLang$prog) [] =
    Delta [] [5;2]``;
val _ = print_eval "gct_shareinst_other"
  ``get_clash_tree (ShareInst Load 5 (Var 2) : 8 wordLang$prog) [] =
    Delta [5] [2]``;
val _ = print_eval "gct_loop"
  ``let a = sptree$fromAList [(1n,())] in
    let b = sptree$fromAList [(2n,())] in
    get_clash_tree (Loop a Skip b : 8 wordLang$prog) [] =
      Seq (Set a) (Seq (Set b) (Seq (Delta [] []) (Set a)))``;
val _ = print_eval "gct_break_none"
  ``get_clash_tree (Break 2 : 8 wordLang$prog) [] = Set sptree$LN``;
val _ = print_eval "gct_break_some"
  ``let a = sptree$fromAList [(1n,())] in
    let b = sptree$fromAList [(2n,())] in
    get_clash_tree (Break 0 : 8 wordLang$prog) [(a,b)] = Set b``;
val _ = print_eval "gct_continue_none"
  ``get_clash_tree (Continue 2 : 8 wordLang$prog) [] = Set sptree$LN``;
val _ = print_eval "gct_continue_some"
  ``let a = sptree$fromAList [(1n,())] in
    let b = sptree$fromAList [(2n,())] in
    get_clash_tree (Continue 0 : 8 wordLang$prog) [(a,b)] = Set a``;
val _ = print_eval "gct_call_none"
  ``get_clash_tree (Call NONE NONE [3;4] NONE : 8 wordLang$prog) [] =
    Set (sptree$insert 3 () (sptree$insert 4 () sptree$LN))``;
val _ = print_eval "gct_call_ret"
  ``let a = sptree$fromAList [(1n,());(2n,())] in
    let b = sptree$fromAList [(3n,())] in
    let cutset = sptree$union a b in
    let args_set = sptree$insert 3 () (sptree$insert 4 () sptree$LN) in
    let live_set = sptree$union cutset args_set in
    get_clash_tree
      (Call (SOME ([7;8],(a,b),Skip,0,0)) NONE [3;4] NONE : 8 wordLang$prog) [] =
      Seq (Set live_set)
        (Seq (Set (sptree$insert 7 () (sptree$insert 8 () cutset)))
          (Delta [] []))``;
val _ = print_eval "gct_call_ret_handler"
  ``let a = sptree$fromAList [(1n,());(2n,())] in
    let b = sptree$fromAList [(3n,())] in
    let cutset = sptree$union a b in
    let args_set = sptree$insert 3 () (sptree$insert 4 () sptree$LN) in
    let live_set = sptree$union cutset args_set in
    get_clash_tree
      (Call (SOME ([7;8],(a,b),Skip,0,0)) NONE [3;4] (SOME (9,Tick,0,0))
        : 8 wordLang$prog) [] =
      Branch (SOME live_set)
        (Seq (Set (sptree$insert 7 () (sptree$insert 8 () cutset)))
          (Delta [] []))
        (Seq (Set (sptree$insert 9 () cutset)) (Delta [] []))``;
