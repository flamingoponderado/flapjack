import Flapjack.Compiler.Backend.ClosTicks.Source
import Flapjack.Compiler.Backend.Semantics.ClosProps.AppCallDests

/-! Call-destination properties of tick removal. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open ClosLang ClosProps

mutual
/-- Structural induction helper for the source theorem, with no separate HOL declaration. -/
private theorem removeSing_appCallDests (selection : Option Bool) (e : Exp) :
    appCallDests selection [removeSing e] = appCallDests selection [e] := by
  cases e with
  | var t n => simp [removeSing, appCallDests]
  | ifThenElse t x y z => simp [removeSing, appCallDests, removeSing_appCallDests selection x, removeSing_appCallDests selection y, removeSing_appCallDests selection z]
  | «let» t xs body => simp [removeSing, appCallDests, removeList_appCallDests selection xs, removeSing_appCallDests selection body]
  | raise t x => simp [removeSing, appCallDests, removeSing_appCallDests selection x]
  | handle t x y => simp [removeSing, appCallDests, removeSing_appCallDests selection x, removeSing_appCallDests selection y]
  | tick t x => simp [removeSing, appCallDests, removeSing_appCallDests selection x]
  | call t ticks dest xs => simp [removeSing, appCallDests, removeList_appCallDests selection xs]
  | app t loc x xs => cases loc <;> simp [removeSing, appCallDests, removeSing_appCallDests selection x, removeList_appCallDests selection xs]
  | fn name loc vs arity body => simp [removeSing, appCallDests, removeSing_appCallDests selection body]
  | letrec names loc vs fns body => simp [removeSing, appCallDests, removeFuns_appCallDests selection fns, removeSing_appCallDests selection body]
  | op t op xs => simp [removeSing, appCallDests, removeList_appCallDests selection xs]
termination_by sizeOf e

/-- List case of the structural induction; it has no separate HOL declaration. -/
private theorem removeList_appCallDests (selection : Option Bool) (xs : List Exp) :
    appCallDests selection (removeList xs) = appCallDests selection xs := by
  cases xs with
  | nil => simp [removeList, appCallDests]
  | cons x xs =>
    simp only [removeList]
    rw [show removeSing x :: removeList xs = [removeSing x] ++ removeList xs from rfl,
      show x :: xs = [x] ++ xs from rfl, appCallDests_append, appCallDests_append,
      removeSing_appCallDests selection x, removeList_appCallDests selection xs]
termination_by sizeOf xs

/-- Recursive-function case of the structural induction, with no separate HOL declaration. -/
private theorem removeFuns_appCallDests (selection : Option Bool) (fns : List (Nat × Exp)) :
    appCallDests selection ((removeFuns fns).map Prod.snd) = appCallDests selection (fns.map Prod.snd) := by
  cases fns with
  | nil => simp [removeFuns, appCallDests]
  | cons pair fns =>
    cases pair with
    | mk arity body =>
      simp only [removeFuns, List.map_cons]
      rw [show removeSing body :: (removeFuns fns).map Prod.snd = [removeSing body] ++ (removeFuns fns).map Prod.snd from rfl,
        show body :: fns.map Prod.snd = [body] ++ fns.map Prod.snd from rfl,
        appCallDests_append, appCallDests_append, removeSing_appCallDests selection body,
        removeFuns_appCallDests selection fns]
termination_by sizeOf fns
decreasing_by all_goals (subst_vars; simp_wf; omega)
end

/-- Tick removal preserves application and call destinations. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_app_call_dests"]
theorem removeSource_appCallDests (selection : Option Bool) (xs : List Exp) :
    appCallDests selection (removeSource xs) = appCallDests selection xs := by
  simpa using removeList_appCallDests selection xs

end Flapjack.Compiler.Backend.ClosTicks
