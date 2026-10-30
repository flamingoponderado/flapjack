(* Types and representative expression-translation cases from pinned HOL. *)
load "word_bignumTheory"; load "wordsLib";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "compile_exp_type="; print_type (type_of ``word_bignum$compile_exp``); print "\n");
fun row name term = (print (name ^ "="); print_term (rhs (concl (EVAL term))); print "\n");
val _ = row "binary" ``word_bignum$compile_exp (wordLang$Op asm$Add [wordLang$Var 33; wordLang$Const (7w:64 word)])``;
val _ = row "unary" ``word_bignum$compile_exp (wordLang$Op asm$Add [wordLang$Var 1] : 64 wordLang$exp)``;
val _ = row "lookup" ``word_bignum$compile_exp (wordLang$Lookup (stackLang$Temp 3w) : 64 wordLang$exp)``;
val _ = row "shift" ``word_bignum$compile_exp (wordLang$Shift ast$Lsl (wordLang$Var 2) (wordLang$Const (3w:64 word)))``;
