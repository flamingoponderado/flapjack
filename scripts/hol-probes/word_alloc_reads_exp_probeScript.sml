(* Direct original word_alloc get_reads_exp, observed through ordered list output. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "var_single" ``get_reads_exp (Var 3 : 8 wordLang$exp)``;
val _ = observe "load_var" ``get_reads_exp (Load (Var 3) : 8 wordLang$exp)``;
val _ = observe "op_nested" ``get_reads_exp
  (Op Add [Var 3; Load (Var 5); Var 3] : 8 wordLang$exp)``;
val _ = observe "shift_order" ``get_reads_exp
  (Shift Lsl (Var 5) (Var 6) : 8 wordLang$exp)``;
val _ = observe "const_empty" ``get_reads_exp (Const 7w : 8 wordLang$exp)``;
val _ = observe "lookup_empty" ``get_reads_exp (Lookup (Temp 9w) : 8 wordLang$exp)``;
val _ = observe "mixed_nested" ``get_reads_exp
  (Op Sub [Load (Shift Lsr (Var 7) (Var 2)); Var 4; Const 9w] : 8 wordLang$exp)``;
