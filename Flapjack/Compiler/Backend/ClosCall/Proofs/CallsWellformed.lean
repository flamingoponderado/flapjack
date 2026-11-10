module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateGrowth
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelDistinct
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

@[expose] public section

/-! Well-formedness preservation by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- Direct-call conversion preserves the source one-sided code invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_wfg'"]
theorem calls_weaklyWellFormed (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g) ∧ everyFnLocationSome xs ∧ weaklyWellFormed g0) :
    weaklyWellFormed g := by
  have bounds := calls_codeSubset xs g0 ys g h.1
  intro label member
  rcases bounds.2.2 member with new | old
  · exact new
  · exact bounds.1 (h.2.2 old)

/-- Direct-call conversion preserves the complete source state invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_wfg"]
theorem calls_wellFormed (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g) ∧ (codeLocations xs).Nodup ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations xs} ∧
        label ∈ g0.2.map Prod.fst)) ∧ everyFnLocationSome xs ∧ wellFormed g0) :
    wellFormed g := by
  have oldWeak : weaklyWellFormed g0 := by
    unfold weaklyWellFormed
    rw [h.2.2.2.2.1]
  have weak := calls_weaklyWellFormed xs g0 ys g ⟨h.1, h.2.2.2.1, oldWeak⟩
  have domain := calls_domain xs g0 ys g h.1
  have labels := calls_codeSubset xs g0 ys g h.1
  have distinct := calls_allDistinct xs g0 ys g ⟨h.1, h.2.2.2.2.2, h.2.1, h.2.2.1⟩
  refine ⟨Set.Subset.antisymm weak ?_, distinct⟩
  rintro _ ⟨loc, present, rfl⟩
  rcases domain present with old | ⟨label, member, previous⟩
  · apply labels.2.1
    rw [h.2.2.2.2.1]
    exact ⟨loc, old, rfl⟩
  · obtain ⟨other, _, same⟩ := weak member
    have equal : loc = other := by
      rw [← same] at previous
      simpa using previous.symm
    rw [equal, same]
    exact member

end Flapjack.Compiler.Backend.ClosCall
