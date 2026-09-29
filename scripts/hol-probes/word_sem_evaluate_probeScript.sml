(*
  Direct HOL-EVAL fixture for wordSem evaluate_def
  (cakeml/compiler/backend/semantics/wordSemScript.sml:1016-1260) ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/Evaluate.lean, at 64-bit words.
  States are record updates of a free state s; each row observes
  (result, toAList locals, clock).
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

val _ = computeLib.add_funs [evaluate_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,num) wordSem$state``;
val ffi = ``<| oracle := (\n (st:num) conf bytes. Oracle_return (st + 1) bytes);
               ffi_state := 0; io_events := [] |>``;
val code = ``fromAList [(5:num, (1:num, Return 0 [0] : 64 wordLang$prog));
                         (6, (2, Return 0 [2]))]``;
val st = ``^s with <|
  locals := fromAList [(2, Word 7w); (3, Loc 5 0); (8, Word 16w); (9, Word 1w)];
  clock := 3; termdep := 2; code := ^code; stack := []; handler := 0;
  store := FEMPTY; locals_size := SOME 0; stack_max := SOME 0; stack_size := LN;
  permute := (\n i. i); memory := (\a. Word 0w); mdomain := {16w}; ffi := ^ffi |>``;
fun evst label p sti =
  print_eval label ``(\(r:64 wordSem$result option, t:(64,'c,num) wordSem$state).
      (r, toAList t.locals, t.clock)) (evaluate (^p, ^sti))``;
fun ev label p = evst label p st;

val _ = ev "skip" ``Skip : 64 wordLang$prog``;
val _ = ev "seq_tick" ``Seq (Assign 1 (Const 5w)) Tick : 64 wordLang$prog``;
val _ = evst "tick_zero" ``Tick : 64 wordLang$prog`` ``^st with clock := 0``;
val _ = ev "if_true" ``If Equal 2 (Imm 7w) (Assign 1 (Const 1w)) (Assign 1 (Const 0w)) : 64 wordLang$prog``;
val _ = ev "if_false" ``If Less 2 (Imm 7w) (Assign 1 (Const 1w)) (Assign 1 (Const 0w)) : 64 wordLang$prog``;
val _ = ev "if_error" ``If Equal 3 (Imm 7w) Skip Skip : 64 wordLang$prog``;
val _ = ev "loop_break" ``Loop (insert 2 () LN) (Break 0) (insert 2 () LN) : 64 wordLang$prog``;
val _ = ev "loop_timeout" ``Loop LN (Continue 0) LN : 64 wordLang$prog``;
val _ = ev "loop_exit" ``Loop LN (Break 1) LN : 64 wordLang$prog``;
val _ = ev "return" ``Return 3 [2] : 64 wordLang$prog``;
val _ = ev "raise_nohandler" ``Raise 2 : 64 wordLang$prog``;
val _ = evst "raise_handler" ``Raise 2 : 64 wordLang$prog``
  ``^st with stack := [StackFrame (SOME 1) [(4, Word 1w)] [(6, Word 2w)] (SOME (0, 7, 8))]``;
val _ = evst "must_terminate_zero" ``MustTerminate Skip : 64 wordLang$prog`` ``^st with termdep := 0``;
val _ = ev "must_terminate" ``MustTerminate (Assign 1 (Const 9w)) : 64 wordLang$prog``;
val _ = ev "move" ``Move 0 [(5, 2); (6, 3)] : 64 wordLang$prog``;
val _ = ev "move_dup" ``Move 0 [(5, 2); (5, 3)] : 64 wordLang$prog``;
val _ = ev "set_get" ``Seq (Set NextFree (Const 4w)) (Get 1 NextFree) : 64 wordLang$prog``;
val _ = ev "set_handler" ``Set Handler (Const 1w) : 64 wordLang$prog``;
val _ = ev "loc_value" ``LocValue 1 5 : 64 wordLang$prog``;
val _ = ev "loc_value_missing" ``LocValue 1 4 : 64 wordLang$prog``;
val _ = ev "store_consts"
  ``StoreConsts 20 21 8 9 [(T, 5w)] : 64 wordLang$prog``;
val _ = ev "call_tail" ``Call NONE (SOME 5) [3] NONE : 64 wordLang$prog``;
val _ = evst "call_tail_timeout" ``Call NONE (SOME 5) [3] NONE : 64 wordLang$prog`` ``^st with clock := 0``;
val _ = ev "call_ret"
  ``Call (SOME ([4], (insert 2 () LN, insert 3 () LN), Skip, 10, 11)) (SOME 6) [2] NONE
      : 64 wordLang$prog``;
val _ = ev "call_ret_empty_names"
  ``Call (SOME ([4], (LN, insert 3 () LN), Skip, 10, 11)) (SOME 6) [2] NONE : 64 wordLang$prog``;
val _ = ev "call_missing" ``Call NONE (SOME 7) [3] NONE : 64 wordLang$prog``;
val _ = ev "ffi_missing_len"
  ``FFI (strlit "f") 8 21 8 21 (insert 2 () LN, LN) : 64 wordLang$prog``;
val _ = ev "ffi_ok"
  ``FFI (strlit "f") 8 9 8 9 (insert 2 () LN, LN) : 64 wordLang$prog``;
