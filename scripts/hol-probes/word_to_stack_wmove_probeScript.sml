load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "wm_empty" ``word_to_stack$wMove [] (3,8,0) = (Skip : 64 word stackLang$prog)``;
val _ = print_eval "wm_self" ``word_to_stack$wMove [(2,3)] (3,8,0) = (Skip : 64 word stackLang$prog)``;
val _ = print_eval "wm_reg" ``word_to_stack$wMove [(2,4)] (3,8,0) = (Inst (Arith (Binop Or 1 2 (Reg 2))) : 64 word stackLang$prog)``;
val _ = print_eval "wm_load" ``word_to_stack$wMove [(2,8)] (3,8,0) = (StackLoad 1 6 : 64 word stackLang$prog)``;
val _ = print_eval "wm_store" ``word_to_stack$wMove [(8,2)] (3,8,0) = (StackStore 1 6 : 64 word stackLang$prog)``;
val _ = print_eval "wm_spill" ``word_to_stack$wMove [(8,10)] (3,8,0) = (Seq (StackLoad 3 5) (StackStore 3 6) : 64 word stackLang$prog)``;
val _ = print_eval "wm_swap" ``word_to_stack$wMove [(2,4);(4,2)] (3,8,0) = (Seq (Inst (Arith (Binop Or 4 2 (Reg 2)))) (Seq (Inst (Arith (Binop Or 2 1 (Reg 1)))) (Inst (Arith (Binop Or 1 4 (Reg 4))))) : 64 word stackLang$prog)``;
val _ = print_eval "wm_spill_swap" ``word_to_stack$wMove [(8,10);(10,8)] (3,8,0) = (Seq (StackLoad 4 5) (Seq (Seq (StackLoad 3 6) (StackStore 3 5)) (StackStore 4 6)) : 64 word stackLang$prog)``;
val _ = print_eval "wm_odd" ``word_to_stack$wMove [(3,5)] (3,8,0) = (Inst (Arith (Binop Or 1 2 (Reg 2))) : 64 word stackLang$prog)``;
val _ = print_eval "wm_underflow" ``word_to_stack$wMove [(2,8)] (3,0,0) = (StackLoad 1 0 : 64 word stackLang$prog)``;
val _ = print_eval "wm_fprime" ``word_to_stack$wMove [(8,10)] (3,8,99) = (Seq (StackLoad 3 5) (StackStore 3 6) : 64 word stackLang$prog)``;
