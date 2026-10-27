load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_type label tm = (print label; Lib.with_flag (Globals.show_types,true) print_type (type_of tm); print "\n");
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_type "thunk_type=" ``flatSem$IsThunk``;
val _ = show_thm "thunk_dest=" flatSemTheory.dest_thunk_def;
val _ = show_thm "thunk_update=" flatSemTheory.update_thunk_def;
val _ = show_thm "thunk_bad=" flatSemTheory.bad_thunk_update_def;
val _ = show_eval "valid_thunk=" ``flatSem$dest_thunk [Loc F 0] [Thunk NotEvaluated (Litv (IntLit 7))]``;
val _ = show_eval "ref_flag=" ``flatSem$dest_thunk [Loc T 0] [Thunk NotEvaluated (Litv (IntLit 7))]``;
val _ = show_eval "bad_index=" ``flatSem$dest_thunk [Loc F 1] [Thunk NotEvaluated (Litv (IntLit 7))]``;
val _ = show_eval "ordinary_ref=" ``flatSem$dest_thunk [Loc T 0] [Refv (Litv (IntLit 7))]``;
val _ = show_eval "nonlocation=" ``flatSem$dest_thunk [Litv (IntLit 3)] []``;
val _ = show_eval "update_value=" ``flatSem$update_thunk [Loc F 0] [Thunk NotEvaluated (Litv (IntLit 7))] [Litv (IntLit 9)]``;
val _ = show_eval "update_nested=" ``flatSem$update_thunk [Loc F 0] [Thunk NotEvaluated (Litv (IntLit 7))] [Loc F 0]``;
