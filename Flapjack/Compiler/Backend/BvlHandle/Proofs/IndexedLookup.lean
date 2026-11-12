module

public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Misc.ListEl
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Indexed association-list facts used by handler environment packing. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs

/-- The element immediately after a prefix is found at the prefix length. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "IMP_EL_SING"]
theorem impElSing {α : Type} (k : Nat) (xs : List α) (x : α) (ys : List α)
    (index : k = xs.length) : @Flapjack.holEl α ⟨x⟩ k (xs ++ [x] ++ ys) = x := by
  let : Nonempty α := ⟨x⟩
  subst k
  rw [Flapjack.holEl_eq_getElem _ _ (by simp)]
  simp

/-- Appending a different key leaves indexed association lookup unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "ALOOKUP_MAPi_SWAP"]
theorem alookupMapIdx_swap {α : Type} (n k : α) (xs : List α) (different : n ≠ k) :
    Flapjack.holALookup ((xs ++ [k]).mapIdx fun i x => (x, i)) n =
      Flapjack.holALookup (xs.mapIdx fun i x => (x, i)) n := by
  classical
  rw [List.mapIdx_concat, Flapjack.holALookup_append]
  cases h : Flapjack.holALookup (xs.mapIdx fun i x => (x, i)) n <;>
    simp [Flapjack.holALookup, different]

/-- A newly appended key receives the preceding list's length as its index. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "ALOOKUP_MAPi_APPEND2"]
theorem alookupMapIdx_append {α : Type} (xs : List α) (k : α) (absent : k ∉ xs) :
    Flapjack.holALookup ((xs ++ [k]).mapIdx fun i x => (x, i)) k = some xs.length := by
  classical
  rw [List.mapIdx_concat, Flapjack.holALookup_append]
  cases h : Flapjack.holALookup (xs.mapIdx fun i x => (x, i)) k with
  | none => simp [Flapjack.holALookup]
  | some v =>
    have member := Flapjack.holALookup_member _ k v h
    obtain ⟨i, hi, eq⟩ := List.mem_mapIdx.mp member
    have keyEq : xs[i] = k := (Prod.mk.inj eq).1
    exact False.elim (absent (keyEq ▸ List.getElem_mem hi))

/-- A successful indexed association lookup returns an in-range index. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "ALOOKUP_MAPi"]
theorem alookupMapIdx_bound {α β : Type} (n : α) (xs : List α) (_i : β) (x : Nat)
    (found : Flapjack.holALookup (xs.mapIdx fun i v => (v, i)) n = some x) : x < xs.length := by
  have member := Flapjack.holALookup_member _ n x found
  obtain ⟨i, hi, eq⟩ := List.mem_mapIdx.mp member
  have eqIndex : i = x := (Prod.mk.inj eq).2
  omega

end Flapjack.Compiler.Backend.BvlHandle.Proofs
