(* Direct original word_alloc$apply_colour_exp_def observations, at 8-bit
   words. Includes nested Op/Load, expression-valued Shift amount, Temp's
   fixed five-bit name, duplicate variables, and empty Op. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "nested"
  ``apply_colour_exp (\n. n + 10)
      (Op Add [Const 7w; Load (Var 3); Lookup (Temp 9w);
        Shift Lsl (Var 5) (Var 6)] : 8 wordLang$exp)``;
val _ = observe "duplicate"
  ``apply_colour_exp (\n. n MOD 2)
      (Op Sub [Var 3; Var 3; Var 4] : 8 wordLang$exp)``;
val _ = observe "empty"
  ``apply_colour_exp (\n. n + 10) (Op Add [] : 8 wordLang$exp)``;
