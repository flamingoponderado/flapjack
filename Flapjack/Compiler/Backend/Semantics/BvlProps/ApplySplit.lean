module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.HolRef

@[expose] public section

/-!
# Application-case splitting for HOL `bvlProps`

Counterpart of `cakeml/compiler/backend/semantics/bvlPropsScript.sml:47-60`: the
local `do_app_split_list` and `pair_lam_lem` helpers that feed HOL's
`do_app_cases_val` / `do_app_cases_err` conversions.
-/

namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace ApplySplitCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ApplySplitCarrier

/-- An application result is its empty-argument or non-empty-argument case. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_split_list"
  (fmap_as_finite_support := [refs])]
theorem doApp_split_list {C F : Type} (op : ClosLang.Op) (vs : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F)
    (res : Result (BvlSem.Value × Flapjack.Compiler.Backend.BvlSem.State C F) BvlSem.Value) :
    doApp op vs s = res ↔
      (vs = [] ∧ doApp op [] s = res) ∨
        ∃ v vs1, vs = v :: vs1 ∧ doApp op (v :: vs1) s = res := by
  cases vs with
  | nil => simp
  | cons v vs1 =>
    constructor
    · intro h
      exact Or.inr ⟨v, vs1, rfl, h⟩
    · rintro (⟨h1, _h2⟩ | ⟨v1, vs11, heq, h⟩)
      · simp at h1
      · cases heq
        exact h

/-- Destructuring a pair in a `let` is the corresponding existential. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "pair_lam_lem"]
theorem pairLamLem {α β γ : Type} (f : α → β → γ) (v : γ) (z : α × β) :
    (let (x, y) := z; f x y) = v ↔ ∃ x1 x2, z = (x1, x2) ∧ f x1 x2 = v := by
  cases z
  constructor
  · intro h
    exact ⟨_, _, rfl, h⟩
  · rintro ⟨x1, x2, heq, h⟩
    cases heq
    exact h

end Flapjack.Compiler.Backend.BvlProps
