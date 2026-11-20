import Flapjack.Compiler.Backend.ClosLang.Syntax
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
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

/-- Destination collection over a cons cell splits at the head. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_call_dests_cons"]
theorem appCallDests_cons (y : List Exp) (x : Exp) (opt : Option Bool) :
    appCallDests opt (x :: y) = appCallDests opt [x] ∪ appCallDests opt y := by
  cases y with
  | nil => simp [appCallDests]
  | cons y' ys => simp [appCallDests]

/-- Destination collection over a cons cell splits at the head for the
`any_dests` overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "any_dest_cons"]
theorem anyDests_cons (y : List Exp) (x : Exp) :
    appCallDests none (x :: y) = appCallDests none [x] ∪ appCallDests none y :=
  appCallDests_cons y x none

/-- Destination collection over a cons cell splits at the head for the
`call_dests` overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "call_dest_cons"]
theorem callDests_cons (y : List Exp) (x : Exp) :
    appCallDests (some true) (x :: y) =
      appCallDests (some true) [x] ∪ appCallDests (some true) y :=
  appCallDests_cons y x (some true)

/-- Destination collection over a cons cell splits at the head for the
`app_dests` overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_dest_cons"]
theorem appDests_cons (y : List Exp) (x : Exp) :
    appCallDests (some false) (x :: y) =
      appCallDests (some false) [x] ∪ appCallDests (some false) y :=
  appCallDests_cons y x (some false)

/-- Destination collection distributes over append for the `any_dests`
overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "any_dest_append"]
theorem anyDests_append (l1 l2 : List Exp) :
    appCallDests none (l1 ++ l2) = appCallDests none l1 ∪ appCallDests none l2 :=
  appCallDests_append none l1 l2

/-- Destination collection distributes over append for the `call_dests`
overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "call_dest_append"]
theorem callDests_append (l1 l2 : List Exp) :
    appCallDests (some true) (l1 ++ l2) =
      appCallDests (some true) l1 ∪ appCallDests (some true) l2 :=
  appCallDests_append (some true) l1 l2

/-- Destination collection distributes over append for the `app_dests`
overload. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_dest_append"]
theorem appDests_append (l1 l2 : List Exp) :
    appCallDests (some false) (l1 ++ l2) =
      appCallDests (some false) l1 ∪ appCallDests (some false) l2 :=
  appCallDests_append (some false) l1 l2

/-- Destination collection over a mapped list unions the per-element
collections. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "app_call_dests_map"]
theorem appCallDests_map {α : Type} (ls : List α) (opt : Option Bool) (f : α → Exp) :
    appCallDests opt (ls.map f) =
      ⋃₀ {s | s ∈ ls.map (fun x => appCallDests opt [f x])} := by
  induction ls with
  | nil => simp [appCallDests]
  | cons x xs ih =>
    rw [List.map_cons, appCallDests_cons, ih]
    ext n
    simp [List.mem_cons, Set.mem_sUnion, Set.mem_union]

end Flapjack.Compiler.Backend.ClosProps
