module

public import Flapjack.Compiler.Inference.TypeDCanon
public import Mathlib.Data.Set.Card

@[expose] public section

/-! Bijections used to allocate canonical type identifiers. -/
namespace Flapjack.Compiler.Inference.TypeDCanon

/-- Cardinalities add on disjoint finite sets. The finiteness premises ensure
that `Set.ncard` agrees with HOL `CARD` for each set in the conclusion. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "DISJOINT_CARD_UNION"]
theorem disjointCardUnion {α : Type} (s t : Set α) :
    s.Finite ∧ t.Finite ∧ Disjoint s t →
      (s ∪ t).ncard = s.ncard + t.ncard := by
  rintro ⟨hs, ht, hd⟩
  exact Set.ncard_union_eq hd hs ht

/-- The datatype case of declaration canonicalization indexes its distinct
type identifiers by their positions in the source list. This Flapjack helper
packages the list-to-range bijection constructed inline in the HOL proof. -/
theorem listIdxOfBij (ids : List Nat) (distinct : ids.Nodup) :
    ({id | id ∈ ids} : Set Nat).Finite ∧
      ({id | id ∈ ids} : Set Nat).ncard = ids.length ∧
      Set.BijOn ids.idxOf (fun id => id ∈ ids) (fun i => i < ids.length) ∧
      ∀ (i : Nat) (h : i < ids.length), ids.idxOf ids[i] = i := by
  have setEq : ({id | id ∈ ids} : Set Nat) = ↑ids.toFinset := by
    ext id
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [setEq]
    exact Finset.finite_toSet _
  · rw [setEq, Set.ncard_coe_finset]
    exact List.toFinset_card_of_nodup distinct
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact List.idxOf_lt_length_of_mem hx
    · intro x hx y hy eq
      have hx' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
      have hy' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
      change ids.idxOf x = ids.idxOf y at eq
      have hx'' : ids[ids.idxOf y]'(List.idxOf_lt_length_of_mem hy) = x := by
        simpa only [eq] using hx'
      exact hx''.symm.trans hy'
    · intro i hi
      exact ⟨ids[i], List.getElem_mem hi, distinct.idxOf_getElem i hi⟩
  · intro i hi
    exact distinct.idxOf_getElem i hi

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
