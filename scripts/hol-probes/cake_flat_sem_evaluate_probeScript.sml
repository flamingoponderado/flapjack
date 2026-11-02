load "flatSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_type "evaluate_type=" ``flatSem$evaluate``;
val _ = show_type "evaluate_dec_type=" ``flatSem$evaluate_dec``;
val _ = show_type "evaluate_decs_type=" ``flatSem$evaluate_decs``;
val _ = show_thm "evaluate_rebound_typed=" flatSemTheory.evaluate_def;
val _ = show_eval "eval_lit=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Lit backend_common$None (IntLit 3)])``;
val _ = show_eval "eval_missing=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Var_local backend_common$None «x»])``;
val _ = show_eval "eval_lookup_shadow=" ``SND (flatSem$evaluate
  <| v := [(«x», Litv (IntLit 1)); («x», Litv (IntLit 2))] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4) [Var_local backend_common$None «x»])``;
val _ = show_eval "eval_let_shadow=" ``SND (flatSem$evaluate
  <| v := [(«x», Litv (IntLit 1))] |> ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Let backend_common$None (SOME «x») (Lit backend_common$None (IntLit 2)) (Var_local backend_common$None «x»)])``;
val _ = show_eval "eval_if_bad=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [If backend_common$None (Lit backend_common$None (IntLit 1)) (Lit backend_common$None (IntLit 2)) (Lit backend_common$None (IntLit 3))])``;
val _ = show_eval "eval_list_raise=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Raise backend_common$None (Lit backend_common$None (IntLit 9)); Lit backend_common$None (IntLit 2)])``;
val _ = show_eval "eval_handle_no_match=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Handle backend_common$None (Raise backend_common$None (Lit backend_common$None (IntLit 9))) []])``;
val _ = show_eval "eval_letrec_duplicate=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Letrec «trace» [(«f», «x», Lit backend_common$None (IntLit 1));
                   («f», «y», Lit backend_common$None (IntLit 2))] (Lit backend_common$None (IntLit 3))])``;
val _ = show_eval "eval_app_bad=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [App backend_common$None (Src Opapp) [Lit backend_common$None (IntLit 1)]])``;
val _ = show_eval "eval_match_duplicate=" ``SND (flatSem$evaluate <| v := [] |>
  ((ARB : (unit,unit) flatSem$state) with clock := 4)
  [Mat backend_common$None (Lit backend_common$None (IntLit 1))
    [(Pas (Pvar «x») «x», Lit backend_common$None (IntLit 3))]])``;
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
