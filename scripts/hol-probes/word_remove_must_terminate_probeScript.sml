load "preamble"; load "word_removeTheory";
open bossLib; open HolKernel Parse; open preamble; open word_removeTheory;

val print_eval = fn label => fn q =>
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

val _ = print_eval "rmt_mt_seq"
  ``remove_must_terminate ((MustTerminate (Seq Skip Tick)) : 8 wordLang$prog)``;
val _ = print_eval "rmt_mt_nested"
  ``remove_must_terminate ((MustTerminate (MustTerminate Tick)) : 8 wordLang$prog)``;
val _ = print_eval "rmt_seq"
  ``remove_must_terminate ((Seq (MustTerminate Skip) (MustTerminate Tick)) : 8 wordLang$prog)``;
val _ = print_eval "rmt_if"
  ``remove_must_terminate ((If Equal 1 (Imm 0w) (MustTerminate Skip) Tick) : 8 wordLang$prog)``;
val _ = print_eval "rmt_loop"
  ``remove_must_terminate ((Loop LN (MustTerminate (Break 0)) LN) : 8 wordLang$prog)``;
val _ = print_eval "rmt_call_ret_handler"
  ``remove_must_terminate ((Call (SOME ([1], (LN,LN), MustTerminate Skip, 2, 3)) NONE [4]
      (SOME (5, MustTerminate Tick, 6, 7))) : 8 wordLang$prog)``;
val _ = print_eval "rmt_call_tail_handler"
  ``remove_must_terminate ((Call NONE (SOME 1) [2] (SOME (3, MustTerminate Skip, 4, 5))) : 8 wordLang$prog)``;
val _ = print_eval "rmt_tick" ``remove_must_terminate (Tick : 8 wordLang$prog)``;
