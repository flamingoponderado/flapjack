import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Mathlib.Data.Nat.Find

/-! BVL constant construction with the original least-fresh allocation rule. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.Basis.Pure.MlString

private theorem natList_bounded (keys : List Nat) : ∃ bound, ∀ key ∈ keys, key < bound := by
  induction keys with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
    obtain ⟨bound, h⟩ := ih
    refine ⟨max first bound + 1, ?_⟩
    intro key member
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have := h key member
      omega

/-- A finite-support BVL reference map has an unallocated natural index. -/
theorem unusedRef_exists (refs : HolFiniteMapExact Nat (Ref Value)) : ∃ index, refs.lookup index = none := by
  classical
  obtain ⟨keys, support⟩ := refs.finiteSupport
  obtain ⟨bound, bounded⟩ := natList_bounded keys
  refine ⟨bound, ?_⟩
  cases h : refs.lookup bound with
  | none => rfl
  | some value =>
    have member := support bound (by simp [h])
    have impossible := bounded bound member
    omega

/-- Least unallocated reference, matching HOL's LEAST over the map domain. -/
noncomputable def leastUnusedRef (refs : HolFiniteMapExact Nat (Ref Value)) : Nat := by
  classical
  exact Nat.find (unusedRef_exists refs)

/-- The chosen reference is unused. -/
theorem leastUnusedRef_unused (refs : HolFiniteMapExact Nat (Ref Value)) :
    refs.lookup (leastUnusedRef refs) = none := by
  classical
  exact Nat.find_spec (unusedRef_exists refs)

/-- Every smaller index is already allocated. -/
theorem leastUnusedRef_minimal (refs : HolFiniteMapExact Nat (Ref Value)) (index : Nat)
    (smaller : index < leastUnusedRef refs) : refs.lookup index ≠ none := by
  classical
  exact Nat.find_min (unusedRef_exists refs) smaller

/-- A free zero slot is the least unused reference. -/
theorem leastUnusedRef_eq_zero (refs : HolFiniteMapExact Nat (Ref Value))
    (free : refs.lookup 0 = none) : leastUnusedRef refs = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (unusedRef_exists refs) free)

/-- A free index with every smaller index occupied is the chosen reference. -/
theorem leastUnusedRef_eq (refs : HolFiniteMapExact Nat (Ref Value)) (index : Nat)
    (free : refs.lookup index = none) (prior : ∀ n, n < index → refs.lookup n ≠ none) :
    leastUnusedRef refs = index := by
  classical
  have upper : leastUnusedRef refs ≤ index := Nat.find_min' (unusedRef_exists refs) free
  have lower : index ≤ leastUnusedRef refs := by
    by_contra h
    have occupied := prior (leastUnusedRef refs) (by omega)
    exact occupied (leastUnusedRef_unused refs)
  exact Nat.le_antisymm upper lower

/-- Source-shaped `do_part`: strings allocate an immutable byte array at the
least unused reference. The returned product contains a canonical finite map;
no supported HOL qualifier currently describes this input/output shape, so
this definition remains untagged. -/
noncomputable def doPart (m : Nat → Value) (part : ClosLang.ConstPart)
    (refs : HolFiniteMapExact Nat (Ref Value)) : Value × HolFiniteMapExact Nat (Ref Value) :=
  match part with
  | .int i => (.number i, refs)
  | .w64 w => (.word64 w, refs)
  | .con tag indices => (.block tag (indices.map m), refs)
  | .str text =>
    let index := leastUnusedRef refs
    (.refPtr true index, refs.updateEq (index, .byteArray true text.explode))

/-- Source-shaped `do_build`: sequentially bind each constructed component.
The product's finite-map result is not covered by an existing qualifier. -/
noncomputable def doBuild (m : Nat → Value) (i : Nat) :
    List ClosLang.ConstPart → HolFiniteMapExact Nat (Ref Value) → Value × HolFiniteMapExact Nat (Ref Value)
  | [], refs => (m (i - 1), refs)
  | part :: rest, refs =>
    let (value, refs) := doPart m part refs
    doBuild (fun key => if key = i then value else m key) (i + 1) rest refs

/-- Source-shaped constant construction with the original zero-valued
initial map. The returned product's finite-map carrier remains unqualified. -/
noncomputable def doBuildConst (parts : List ClosLang.ConstPart)
    (refs : HolFiniteMapExact Nat (Ref Value)) : Value × HolFiniteMapExact Nat (Ref Value) :=
  doBuild (fun _ => .number 0) 0 parts refs

end Flapjack.Compiler.Backend.BvlSem
