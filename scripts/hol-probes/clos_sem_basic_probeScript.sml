load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "apply_typed=" closSemTheory.do_app_def;
val _ = show_thm "make_const_typed=" closSemTheory.make_const_def;
val _ = show_thm "get_global_typed=" closSemTheory.get_global_def;
val _ = show_thm "unit_typed=" closSemTheory.Unit_def;
val _ = show_eval "taglen=" ``case closSem$do_app (BlockOp (TagLenEq 2 1)) [Block 2 [Number 9]] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "length=" ``case closSem$do_app (BlockOp (LenEq 1)) [Block 4 [Number 9]] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_test=" ``case closSem$do_app (BlockOp (BoolTest Equal)) [Block 0 []; Block 1 []] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_test_equal=" ``case closSem$do_app (BlockOp (BoolTest Equal)) [Block 1 []; Block 1 []] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_test_invalid=" ``case closSem$do_app (BlockOp (BoolTest Equal)) [Block 2 []; Block 1 []] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_not_false=" ``case closSem$do_app (BlockOp BoolNot) [Block 0 []] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "bool_not_invalid=" ``case closSem$do_app (BlockOp BoolNot) [Block 1 [Number 0]] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "extend=" ``case closSem$do_app (BlockOp (ConsExtend 2)) [Block 0 [Number 1;Number 2;Number 3]; Number 1;Number 2;Number 3;Number 8] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "extend_invalid=" ``case closSem$do_app (BlockOp (ConsExtend 2)) [Block 0 [Number 1]; Number 1;Number 2;Number 2] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "constant=" ``case closSem$do_app (BlockOp (Constant (ConstCons 4 [ConstInt 3; ConstInt 7]))) [] (ARB : (unit,unit) closSem$state) of Rval (v,_) => SOME v | _ => NONE``;
val _ = show_eval "constant_bytes=" ``closSem$make_const (ConstCons 4 [ConstInt (~3); ConstWord64 18446744073709551615w; ConstStr (strlit [CHR 0; CHR 128; CHR 255])])``;
val _ = show_eval "global_present=" ``closSem$get_global 0 [SOME (3:num); NONE]``;
val _ = show_eval "global_empty=" ``closSem$get_global 1 [SOME (3:num); NONE]``;
val _ = show_eval "global_out_of_bounds=" ``closSem$get_global 2 [SOME (3:num); NONE]``;
val _ = show_thm "build_fallback_typed=" (prove (
  ``∀parts values (s : ('c,'ffi) closSem$state).
      closSem$do_app (BlockOp (Build parts)) values s = Rerr (Rabort Rtype_error)``,
  simp [closSemTheory.do_app_def]));
