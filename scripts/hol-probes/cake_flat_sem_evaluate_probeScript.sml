load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "eval_lit=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Lit backend_common$None (IntLit 3)])``;
val _ = show_eval "eval_missing=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Var_local backend_common$None «x»])``;
val _ = show_eval "eval_call=" ``(λ(s,r). (s.clock,r)) (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [App backend_common$None (Src Opapp)
    [Fun «unused» «x» (Var_local backend_common$None «x»); Lit backend_common$None (IntLit 7)]])``;
val _ = show_eval "eval_timeout=" ``(λ(s,r). (s.clock,r)) (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 0)
  [App backend_common$None (Src Opapp)
    [Fun «unused» «x» (Var_local backend_common$None «x»); Lit backend_common$None (IntLit 7)]])``;
val _ = show_eval "eval_raise_handle=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Handle backend_common$None (Raise backend_common$None (Lit backend_common$None (IntLit 8)))
     [(Pvar «x», Var_local backend_common$None «x»)]])``;
val _ = show_eval "eval_reference_order=" ``(λ(s,r). (s.refs,r)) (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with <| clock := 4; refs := [] |>)
  [Con backend_common$None NONE
    [App backend_common$None (Src Opref) [Lit backend_common$None (IntLit 1)];
     App backend_common$None (Src Opref) [Lit backend_common$None (IntLit 2)]]])``;
val _ = show_eval "eval_match_failure=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Mat backend_common$None (Lit backend_common$None (IntLit 1)) []])``;
val _ = show_eval "eval_force=" ``(λ(s,r). (s.clock,s.refs,r)) (flatSem$evaluate <| v := [(«t»,Loc F 0)] |>
  ((ARB : (unit,unit) flatSem$state) with
    <| clock := 4; refs := [Thunk NotEvaluated (Closure <| v := [] |> «u» (Lit backend_common$None (IntLit 5)))] |>)
  [App backend_common$None (Src (ThunkOp ForceThunk)) [Var_local backend_common$None «t»]])``;
val _ = show_eval "eval_decs_unit=" ``SND (flatSem$evaluate_decs
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Con backend_common$None NONE []])``;
val _ = show_eval "eval_decs_nonunit=" ``SND (flatSem$evaluate_decs
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Lit backend_common$None (IntLit 1)])``;
