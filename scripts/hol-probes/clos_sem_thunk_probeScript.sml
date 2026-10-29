load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "dest_typed=" closSemTheory.dest_thunk_def;
val _ = show_thm "store_typed=" closSemTheory.store_thunk_def;
val _ = show_thm "update_typed=" closSemTheory.update_thunk_def;
val _ = show_thm "bad_typed=" closSemTheory.bad_thunk_update_def;
val _ = show_eval "missing=" ``closSem$dest_thunk [RefPtr F 0] FEMPTY``;
val _ = show_eval "ref_flag=" ``closSem$dest_thunk [RefPtr T 0]
  (FEMPTY |+ (0,Thunk NotEvaluated (Number 5)))``;
val _ = show_eval "unevaluated=" ``closSem$dest_thunk [RefPtr F 0]
  (FEMPTY |+ (0,Thunk NotEvaluated (Number 5)))``;
val _ = show_eval "array=" ``closSem$dest_thunk [RefPtr T 0]
  (FEMPTY |+ (0,ValueArray [Number 5]))``;
val _ = show_eval "update=" ``OPTION_MAP (\refs. FLOOKUP refs 0)
  (closSem$update_thunk [RefPtr F 0] (FEMPTY |+ (0,Thunk NotEvaluated (Number 5))) [Number 7])``;
val _ = show_eval "repeat_update=" ``IS_NONE
  (closSem$update_thunk [RefPtr F 0] (FEMPTY |+ (0,Thunk Evaluated (Number 5))) [Number 7])``;
val _ = show_eval "nested_update=" ``IS_NONE
  (closSem$update_thunk [RefPtr F 0] (FEMPTY |+ (0,Thunk NotEvaluated (Number 5))) [RefPtr F 0])``;
