(* Direct HOL-EVAL fixture for crep_to_loop$compile_exp_def. *)
load "bossLib";
load "preamble";
load "crep_to_loopTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open crep_to_loopTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val ct = ``context FEMPTY FEMPTY 0 RISC_V``;
val live = ``insert 2 () (insert 1 () LN)``;

val _ = print_eval "base" ``compile_exp ^ct 5 ^live (BaseAddr : 8 word crepLang$exp)``;
val _ = print_eval "var_hit" ``compile_exp (context (FEMPTY |+ (1, 7)) FEMPTY 0 RISC_V) 5 ^live (Var 1 : 8 word crepLang$exp)``;
val _ = print_eval "load32" ``compile_exp ^ct 5 ^live (Load32 (Const (3w : 8 word)))``;
val _ = print_eval "op_nary" ``compile_exp ^ct 5 ^live (Op Add [Const (1w : 8 word); Const 2w; Const 3w])``;
val _ = print_eval "crepop_mul" ``compile_exp ^ct 5 ^live (Crepop Mul [Const (6w : 8 word); Const 7w])``;
val _ = print_eval "cmp" ``compile_exp ^ct 5 ^live (Cmp Equal (Const (1w : 8 word)) (Const 0w))``;
val _ = print_eval "shift" ``compile_exp ^ct 5 ^live (Shift Lsl (Const (2w : 8 word)) (Const 1w))``;
val _ = print_eval "compile_exps" ``compile_exps ^ct 5 ^live [BaseAddr; Const (1w : 8 word)]``;
