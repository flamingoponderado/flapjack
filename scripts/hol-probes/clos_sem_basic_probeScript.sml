load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "apply_typed=" closSemTheory.do_app_def;
val _ = show_eval "taglen=" ``case closSem$do_app (BlockOp (TagLenEq 2 1)) [Block 2 [Number 9]] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "length=" ``case closSem$do_app (BlockOp (LenEq 1)) [Block 4 [Number 9]] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_test=" ``case closSem$do_app (BlockOp (BoolTest Equal)) [Block 0 []; Block 1 []] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "extend=" ``case closSem$do_app (BlockOp (ConsExtend 2)) [Block 0 [Number 1;Number 2;Number 3]; Number 1;Number 2;Number 3;Number 8] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "extend_invalid=" ``case closSem$do_app (BlockOp (ConsExtend 2)) [Block 0 [Number 1]; Number 1;Number 2;Number 2] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "constant=" ``case closSem$do_app (BlockOp (Constant (ConstCons 4 [ConstInt 3; ConstInt 7]))) [] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
