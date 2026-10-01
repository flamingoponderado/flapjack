(* Finite original compile_single pre-allocation stage observations. These do
   not assert cross-language allocator correctness or source-image closure. *)
load "bossLib"; load "preamble"; load "word_to_wordTheory";
open HolKernel Parse bossLib preamble word_to_wordTheory word_allocTheory
  word_cseTheory word_copyTheory word_unreachTheory;
fun out label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
fun stages n p = ``remove_dead_prog (remove_unreach (three_to_two_reg_prog F
  (copy_prop (word_common_subexp_elim (remove_dead_prog
    (full_ssa_cc_trans ^n ^p))))))``;
val _ = out "allocator_stages_skip" (stages ``0n`` ``(Skip:8 wordLang$prog)``);
val _ = out "allocator_stages_tick" (stages ``0n`` ``(Tick:8 wordLang$prog)``);
val _ = out "allocator_stages_raise" (stages ``2n`` ``(Raise 2:8 wordLang$prog)``);
val _ = out "allocator_stages_tail_call"
  (stages ``2n`` ``(Call NONE (SOME 7) [0;2] NONE:8 wordLang$prog)``);
