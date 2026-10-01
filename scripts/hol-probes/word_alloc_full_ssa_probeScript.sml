(* Original word_alloc full_ssa_cc_trans over representative 64-bit programs
   (limit_var, setup_ssa entry move, ssa_cc_trans body). CakeML remains
   read-only; sparse trees print raw. *)
load "bossLib";
load "wordsLib";
load "word_allocTheory";
open HolKernel Parse boolLib bossLib word_allocTheory;
val _ = Globals.linewidth := 3000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val _ = observe "fs_skip" ``full_ssa_cc_trans 0 (Skip : 64 wordLang$prog)``;
val _ = observe "fs_args" ``full_ssa_cc_trans 2 (Return 0 [2] : 64 wordLang$prog)``;
val _ = observe "fs_assign" ``full_ssa_cc_trans 2 (Seq (Assign 6 (Op Add [Var 0; Var 2])) (Return 0 [6]) : 64 wordLang$prog)``;
val _ = observe "fs_if" ``full_ssa_cc_trans 1 (Seq (If Equal 0 (Imm 0w) (Assign 2 (Const 1w)) (Assign 2 (Const 2w))) (Return 0 [2]) : 64 wordLang$prog)``;
val _ = observe "fs_big" ``full_ssa_cc_trans 1 (Seq (Assign 21 (Var 0)) (Return 0 [21]) : 64 wordLang$prog)``;
