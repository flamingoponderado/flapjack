(*
  Direct HOL-EVAL fixture for the wordSem code-lookup/GC/allocation helpers
  ported in Flapjack/Compiler/Backend/Semantics/WordSem/Alloc.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:614-705) at 64-bit
  words.  States are record updates of a free state `s`; rows observe
  projections.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,'ffi) wordSem$state``;
val code = ``insert 5 (1:num, Skip : 64 wordLang$prog) (insert 3 (2, Tick) LN)``;
val ssize = ``insert 5 (7:num) LN``;

val _ = print_eval "find_code_some"
  ``find_code (SOME 3) [Word 1w : 64 word_loc; Word 2w] ^code ^ssize``;
val _ = print_eval "find_code_some_arity" ``find_code (SOME 3) [Word 1w : 64 word_loc] ^code ^ssize``;
val _ = print_eval "find_code_some_missing" ``find_code (SOME 4) [] ^code ^ssize``;
val _ = print_eval "find_code_none_nil" ``find_code NONE [] ^code ^ssize``;
val _ = print_eval "find_code_none_loc"
  ``find_code NONE [Word 1w : 64 word_loc; Loc 5 0] ^code ^ssize``;
val _ = print_eval "find_code_none_offset"
  ``find_code NONE [Word 1w : 64 word_loc; Loc 5 1] ^code ^ssize``;
val _ = print_eval "find_code_none_arity" ``find_code NONE [Loc 5 0 : 64 word_loc] ^code ^ssize``;
val _ = print_eval "find_code_none_word" ``find_code NONE [Word 5w : 64 word_loc] ^code ^ssize``;
val stk = ``[StackFrame (SOME 1) [(9, Word 9w)] [(2, Word 1w); (4, Loc 1 0)] NONE;
             StackFrame NONE [] [(6, Word 3w : 64 word_loc)] (SOME (1,2,3))]``;
val _ = print_eval "enc_stack" ``enc_stack ^stk``;
val _ = print_eval "dec_stack_hit" ``dec_stack [Word 7w; Word 8w; Loc 3 3] ^stk``;
val _ = print_eval "dec_stack_short" ``dec_stack [Word 7w; Word 8w] ^stk``;
val _ = print_eval "dec_stack_extra" ``dec_stack [Word 7w; Word 8w; Loc 3 3; Word 0w] ^stk``;
val gcrev = ``\(wl:64 word_loc list, m:64 word -> 64 word_loc, d:64 word set,
                 st:store_name |-> 64 word_loc). SOME (REVERSE wl, m, st)``;
val _ = print_eval "gc_rev"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. t.stack)
      (gc (^s with <| stack := ^stk; gc_fun := ^gcrev |>))``;
val _ = print_eval "gc_fail"
  ``gc (^s with <| stack := ^stk; gc_fun := (\x. NONE) |>) = NONE``;
val st = ``^s with store := FEMPTY |+ (NextFree, Word 8w) |+ (TriggerGC, Word 24w)``;
val _ = print_eval "has_space_yes" ``has_space (Word (16w:word64)) ^st``;
val _ = print_eval "has_space_no" ``has_space (Word (17w:word64)) ^st``;
val _ = print_eval "has_space_loc" ``has_space (Loc 0 0 : 64 word_loc) ^st``;
val _ = print_eval "has_space_missing" ``has_space (Word (1w:word64)) (^s with store := FEMPTY)``;
val gcid = ``\(wl:64 word_loc list, m:64 word -> 64 word_loc, d:64 word set,
               st:store_name |-> 64 word_loc). SOME (wl, m, st)``;
val ast = ``^st with <| locals := insert 2 (Word 5w) (insert 4 (Loc 1 0) LN);
                        stack := []; locals_size := SOME 3; stack_max := NONE;
                        permute := (\n i. i); gc_fun := ^gcid |>``;
val proj = ``\(r:64 wordSem$result option, t:(64,'c,'ffi) wordSem$state).
                (r, toAList t.locals, LENGTH t.stack, FLOOKUP t.store AllocSize)``;
val _ = print_eval "alloc_ok" ``^proj (alloc 16w (insert 2 () LN, insert 4 () LN) ^ast)``;
val _ = print_eval "alloc_space" ``^proj (alloc 17w (insert 2 () LN, LN) ^ast)``;
val _ = print_eval "alloc_cut" ``^proj (alloc 16w (insert 3 () LN, LN) ^ast)``;
val _ = print_eval "alloc_gc"
  ``^proj (alloc 16w (LN, LN) (^ast with gc_fun := (\x. NONE)))``;
val _ = print_eval "assign"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. toAList t.locals)
      (assign 1 (Op Add [Var 2; Const 3w]) (^s with locals := insert 2 (Word 5w) LN))``;
val _ = print_eval "assign_fail" ``assign 1 (Var 9) (^s with locals := LN) = NONE``;
