import Flapjack.Compiler.Backend.ClosLang.Syntax
import Mathlib.Data.Set.Basic
import Lean.Elab.Tactic.Omega

/-! Source closure application and call destinations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosLang

private theorem sizeOf_map_snd_le (functions : List (Nat × Exp)) :
    sizeOf (functions.map Prod.snd) ≤ sizeOf functions := by
  induction functions with
  | nil => simp
  | cons entry rest ih =>
    cases entry
    simp_wf
    omega

/-- Collect direct call and application destinations according to the
original optional selection mode. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_call_dests_def" 3590]
def appCallDests (opt : Option Bool) : List Exp → Set Nat
  | [] => ∅
  | x :: y :: xs => appCallDests opt [x] ∪ appCallDests opt (y :: xs)
  | [.var _ _] => ∅
  | [.ifThenElse _ a b c] =>
    (appCallDests opt [a] ∪ appCallDests opt [b]) ∪ appCallDests opt [c]
  | [.let _ xs body] => appCallDests opt xs ∪ appCallDests opt [body]
  | [.raise _ body] => appCallDests opt [body]
  | [.tick _ body] => appCallDests opt [body]
  | [.op _ _ xs] => appCallDests opt xs
  | [.app _ loc fn args] =>
    (if opt = some true then ∅ else match loc with | some n => {n} | none => ∅) ∪
      appCallDests opt [fn] ∪ appCallDests opt args
  | [.fn _ _ _ _ body] => appCallDests opt [body]
  | [.letrec _ _ _ functions body] => appCallDests opt (functions.map Prod.snd) ∪ appCallDests opt [body]
  | [.handle _ a b] => appCallDests opt [a] ∪ appCallDests opt [b]
  | [.call _ _ dest args] =>
    if opt = some false then appCallDests opt args else insert dest (appCallDests opt args)
termination_by expressions => sizeOf expressions
decreasing_by
  all_goals try simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals have bound := sizeOf_map_snd_le functions
  all_goals omega

/-- Destination collection distributes over list append. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_call_dests_append"]
theorem appCallDests_append (opt : Option Bool) (xs ys : List Exp) :
    appCallDests opt (xs ++ ys) = appCallDests opt xs ∪ appCallDests opt ys := by
  induction xs with
  | nil => simp [appCallDests]
  | cons x xs ih =>
    cases xs with
    | nil => cases ys <;> simp [appCallDests]
    | cons y rest =>
      simp only [List.cons_append, appCallDests]
      simp only [List.cons_append] at ih
      rw [ih]
      simp [Set.union_assoc]

end Flapjack.Compiler.Backend.ClosProps
