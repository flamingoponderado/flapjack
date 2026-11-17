module

public import Flapjack.Compiler.Inference.TypeDCanon
public import Mathlib.Data.Set.Card

@[expose] public section

/-! Bijections used to allocate canonical type identifiers. -/
namespace Flapjack.Compiler.Inference.TypeDCanon

/-- Extend disjoint bijections to consecutive ranges of type identifiers.
The `g` bijection embeds `ids` into a finite count, so `ids` is finite whenever
the premise holds. On that domain `Set.ncard` agrees with HOL `CARD`; HOL's
unspecified infinite-set value cannot affect a satisfying premise. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "BIJ_extend_bij"]
theorem bijExtendBij (tids ids : Set Nat) (f g : Nat → Nat) (n : Nat) :
    (∀ id, tids id → ids id → False) ∧
      Set.BijOn f tids (fun id => id < n) ∧
      Set.BijOn g ids (fun id => id < ids.ncard) →
      Set.BijOn (extendBij f g ids n) (fun id => tids id ∨ ids id)
        (fun id => id < n + ids.ncard) := by
  classical
  rintro ⟨disjoint, ⟨mapsF, injF, surjF⟩, ⟨mapsG, injG, surjG⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x member
    change tids x ∨ ids x at member
    change extendBij f g ids n x < n + ids.ncard
    rcases member with hx | hx
    · have absent : ¬ ids x := fun present => disjoint x hx present
      simp only [extendBij, if_neg absent]
      have bound : f x < n := mapsF hx
      omega
    · change ids x at hx
      simp only [extendBij, if_pos hx]
      have bound : g x < ids.ncard := mapsG hx
      omega
  · intro x hx y hy equal
    by_cases ix : ids x <;> by_cases iy : ids y
    · have h : g x = g y := by
        have h' : n + g x = n + g y := by simpa [extendBij, ix, iy] using equal
        omega
      exact injG ix iy h
    · have hyT : tids y := hy.resolve_right iy
      have bound : f y < n := mapsF hyT
      have h : n + g x = f y := by simpa [extendBij, ix, iy] using equal
      omega
    · have hxT : tids x := hx.resolve_right ix
      have bound : f x < n := mapsF hxT
      have h : f x = n + g y := by simpa [extendBij, ix, iy] using equal
      omega
    · have hxT : tids x := hx.resolve_right ix
      have hyT : tids y := hy.resolve_right iy
      apply injF hxT hyT
      simpa [extendBij, ix, iy] using equal
  · intro value bound
    change value < n + ids.ncard at bound
    by_cases lower : value < n
    · obtain ⟨x, hx, equal⟩ := surjF lower
      have absent : ¬ ids x := fun present => disjoint x hx present
      exact ⟨x, Or.inl hx, by simpa [extendBij, absent] using equal⟩
    · have shifted : value - n < ids.ncard := by omega
      obtain ⟨x, hx, equal⟩ := surjG shifted
      change ids x at hx
      refine ⟨x, Or.inr hx, ?_⟩
      simp only [extendBij, if_pos hx, equal]
      omega

end Flapjack.Compiler.Inference.TypeDCanon
