(*
  Direct HOL-EVAL fixture for the wordSem call/loop helpers ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/CallHelpers.lean
  (cakeml/compiler/backend/semantics/wordSemScript.sml:946-1014) at 64-bit
  words; MustTerminate_limit ([nocompute]) is unfolded at width 1.
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

val _ = print_eval "add_ret_loc_none" ``add_ret_loc NONE [Word 1w : 64 word_loc]``;
val _ = print_eval "add_ret_loc_some"
  ``add_ret_loc (SOME ([1;2], (LN,LN), Skip : 64 wordLang$prog, 5:num, 6:num)) [Word 1w : 64 word_loc]``;
val _ = print_eval "bad_dest_args_nil" ``bad_dest_args NONE []``;
val _ = print_eval "bad_dest_args_dest" ``bad_dest_args (SOME 3) []``;
val _ = print_eval "bad_dest_args_args" ``bad_dest_args NONE [1]``;
val _ = print_eval "const_addresses_hit"
  ``const_addresses (8w:word64) [(T,1w);(F,2w)] {8w; 16w}``;
val _ = print_eval "const_addresses_miss"
  ``const_addresses (8w:word64) [(T,1w);(F,2w)] {8w}``;
val _ = print_eval "const_addresses_nil" ``const_addresses (8w:word64) [] {}``;
val _ = print_eval "const_writes"
  ``(\m. (m 8w, m 16w, m 24w))
      (const_writes (8w:word64) 100w [(T,1w);(F,2w)] (\a. Loc 0 0))``;
val _ = print_eval "stop" ``STOP (5:num)``;
val _ = print_eval "bad_fun_return_none" ``bad_fun_return (NONE : 64 wordSem$result option)``;
val _ = print_eval "bad_fun_return_break" ``bad_fun_return (SOME (Break 1 : 64 wordSem$result))``;
val _ = print_eval "bad_fun_return_cont" ``bad_fun_return (SOME (Continue 0 : 64 wordSem$result))``;
val _ = print_eval "bad_fun_return_timeout" ``bad_fun_return (SOME (TimeOut : 64 wordSem$result))``;
val _ = print_eval "bad_fun_return_result" ``bad_fun_return (SOME (Result (Word 0w) [] : 64 wordSem$result))``;
val _ = print_eval "cont_loop_none" ``cont_loop (NONE : 64 wordSem$result option)``;
val _ = print_eval "cont_loop_zero" ``cont_loop (SOME (Continue 0 : 64 wordSem$result))``;
val _ = print_eval "cont_loop_two" ``cont_loop (SOME (Continue 2 : 64 wordSem$result))``;
val _ = print_eval "cont_loop_break" ``cont_loop (SOME (Break 0 : 64 wordSem$result))``;
val _ = print_eval "exit_loop_break0" ``exit_loop (SOME (Break 0 : 64 wordSem$result))``;
val _ = print_eval "exit_loop_break3" ``exit_loop (SOME (Break 3 : 64 wordSem$result))``;
val _ = print_eval "exit_loop_cont1" ``exit_loop (SOME (Continue 1 : 64 wordSem$result))``;
val _ = print_eval "exit_loop_timeout" ``exit_loop (SOME (TimeOut : 64 wordSem$result))``;
val _ = print_eval "exit_loop_none" ``exit_loop (NONE : 64 wordSem$result option)``;
val th = (REWRITE_CONV [MustTerminate_limit_def] THENC EVAL) ``MustTerminate_limit (:1)``;
val _ = (print "must_terminate_limit_1="; print_term (rhs (concl th)); print "\n");
