(* Original HOL word_alloc (word_allocScript.sml:1791-1807): type and EVAL results on small
   64-bit programs, for each allocator branch (Simple, IRC, linear scan), an accepted and a
   clashing oracle colouring, and stack and physical variables. HOL's free asm_config is
   only read through its ISA field. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
val _ = Globals.linewidth := 4000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
fun observe_type label term = (print (label ^ "="); print_type (type_of term); print "\n");
val _ = observe_type "wa_type" ``word_alloc``;
val p1 = ``Seq (Move 0 [(5,9)]) (Inst (Arith (Binop Add 13 5 (Reg 9)))) : 64 wordLang$prog``;
val p2 = ``Seq (Inst (Const 7 3w)) (Seq (Inst (Const 5 4w)) (Inst (Arith (Binop Sub 9 5 (Reg 7))))) : 64 wordLang$prog``;
val p3 = ``Seq (Move 1 [(5,2)]) (Seq (Inst (Arith (Binop Add 2 5 (Imm 1w)))) (Return 0 [2])) : 64 wordLang$prog``;
val _ = observe "wa_simple" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 0 3 ^p1 NONE``;
val _ = observe "wa_irc" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 2 3 ^p1 NONE``;
val _ = observe "wa_linear" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 4 3 ^p1 NONE``;
val _ = observe "wa_oracle_ok" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 0 3 ^p1 (SOME (fromAList [(5,1);(9,2);(13,3)]))``;
val _ = observe "wa_oracle_clash" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 0 3 ^p1 (SOME (fromAList [(5,1);(9,1);(13,3)]))``;
val _ = observe "wa_stack_irc" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 3 1 ^p2 NONE``;
val _ = observe "wa_stack_linear" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 5 1 ^p2 NONE``;
val _ = observe "wa_phys" ``word_alloc 0 ((c:64 asm_config) with ISA := RISC_V) 2 3 ^p3 NONE``;
