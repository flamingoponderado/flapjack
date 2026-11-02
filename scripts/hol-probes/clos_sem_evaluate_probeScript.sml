load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
fun typ label tm = (print label; print_type (type_of tm); print "\n");
val _ = typ "state_globals_type=" ``λ(s:('c,'ffi) closSem$state). s.globals``;
val _ = typ "state_refs_type=" ``λ(s:('c,'ffi) closSem$state). s.refs``;
val _ = typ "state_ffi_type=" ``λ(s:('c,'ffi) closSem$state). s.ffi``;
val _ = typ "state_clock_type=" ``λ(s:('c,'ffi) closSem$state). s.clock``;
val _ = typ "state_compile_type=" ``λ(s:('c,'ffi) closSem$state). s.compile``;
val _ = typ "state_oracle_type=" ``λ(s:('c,'ffi) closSem$state). s.compile_oracle``;
val _ = typ "state_code_type=" ``λ(s:('c,'ffi) closSem$state). s.code``;
val _ = typ "state_max_app_type=" ``λ(s:('c,'ffi) closSem$state). s.max_app``;
val _ = show_thm "dec_clock_typed=" closSemTheory.dec_clock_def;
val _ = show_thm "fix_clock_typed=" closSemTheory.fix_clock_def;
val _ = show_thm "initial_state_typed=" closSemTheory.initial_state_def;
val _ = show_thm "evaluate_typed=" closSemTheory.evaluate_def;
val _ = show_eval "variable=" ``FST (closSem$evaluate ([Var None 0],[Number 7],ARB : (unit,unit) closSem$state))``;
val _ = show_eval "missing=" ``FST (closSem$evaluate ([Var None 1],[Number 7],ARB : (unit,unit) closSem$state))``;
val _ = show_eval "conditional=" ``FST (closSem$evaluate ([If None (Op None (BlockOp (Cons 1)) []) (Op None (IntOp (Const 7)) []) (Op None (IntOp (Const 9)) [])],[],ARB : (unit,unit) closSem$state))``;
val _ = show_eval "raise_handle=" ``FST (closSem$evaluate ([Handle None (Raise None (Op None (IntOp (Const 7)) [])) (Var None 0)],[],ARB : (unit,unit) closSem$state))``;
val _ = show_eval "zero_tick=" ``FST (closSem$evaluate ([Tick None (Var None 0)],[Number 7],(ARB : (unit,unit) closSem$state) with clock := 0))``;
val _ = show_eval "call_closure=" ``FST (closSem$evaluate ([App None NONE (Fn «f» NONE NONE 1 (Var None 0)) [Op None (IntOp (Const 9)) []]],[],(ARB : (unit,unit) closSem$state) with <|clock := 2; max_app := 2|>))``;
