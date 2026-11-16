(* Original CakeML computational walker, including its one-step result. *)
load "unifyTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;

fun show label tm =
  (print (label ^ "="); print_term (rhs (concl (EVAL tm))); print "\n");

val _ = show "code_none" ``unify$cvwalk_code (LN :infer_t num_map) 7``;
val _ = show "code_db" ``unify$cvwalk_code (insert 2 (Infer_Tvar_db 4) LN) 2``;
val _ = show "code_app" ``unify$cvwalk_code (insert 2 (Infer_Tapp [Infer_Tuvar 3] 5) LN) 2``;
val _ = show "code_var" ``unify$cvwalk_code (insert 2 (Infer_Tuvar 7) LN) 2``;
val _ = show "walk_chain" ``unify$tcvwalk (insert 2 (Infer_Tuvar 7) (insert 7 (Infer_Tvar_db 4) LN)) 2``;
val _ = show "occurs_empty" ``unify$tcocwl (LN :infer_t num_map) 3 [[]]``;
val _ = show "occurs_var" ``unify$tcocwl (LN :infer_t num_map) 3 [[Infer_Tuvar 3]]``;
val _ = show "occurs_db" ``unify$tcocwl (LN :infer_t num_map) 3 [[Infer_Tvar_db 3]]``;
val _ = show "occurs_nested" ``unify$tcocwl (LN :infer_t num_map) 3 [[Infer_Tapp [Infer_Tvar_db 2; Infer_Tapp [Infer_Tuvar 3] 5] 4]]``;
val _ = show "occurs_chain" ``unify$tcocwl (insert 2 (Infer_Tuvar 7) LN) 7 [[Infer_Tuvar 2]]``;
