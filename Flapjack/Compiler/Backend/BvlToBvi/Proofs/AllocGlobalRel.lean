import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AllocGlobalStub

/-! State relation after global-array growth. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Growing the represented global array preserves the BVL-to-BVI state
relation when the replacement pointer is fresh or is the old global pointer. -/
theorem stateRel_allocGlobal {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr newPtr count extra : Nat) (fields : List Value)
    (related : stateRel relocate source target) (global : target.global = some ptr)
    (lookup : target.refs.lookup ptr = some (.valueArray
      (.number (Int.ofNat (source.globals.length + 1)) :: fields)))
    (fresh : newPtr ≠ ptr → target.refs.lookup newPtr = none)
    (capacity : source.globals.length + count + 1 ≤ fields.length + extra) :
    stateRel relocate { source with globals := source.globals ++ List.replicate count none }
      { target with
        global := some newPtr
        refs := (target.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (source.globals.length + count + 1)) :: fields))).updateEq
          (newPtr, .valueArray (.number (Int.ofNat (source.globals.length + count + 1)) :: fields ++ List.replicate extra (.number 0))) } := by
  obtain ⟨oldSeparate, oldSize, oldLookup, oldBound⟩ := related.2.2.1 ptr global
  have fieldsEq : fields = source.globals.map (fun value => (value.map (adjustBv relocate)).getD (.number 0)) ++
      List.replicate (oldSize - (source.globals.length + 1)) (.number 0) := by
    rw [lookup] at oldLookup
    simpa using oldLookup
  have newSeparate : ∀ key, source.refs.lookup key ≠ none → newPtr ≠ relocate key := by
    intro key present equal
    by_cases same : newPtr = ptr
    · exact oldSeparate key present (same.symm.trans equal)
    · have targetPresent := related.1.1 key present
      rw [← equal, fresh same] at targetPresent
      contradiction
  have oldRel := refsRel_writeGlobal relocate source.refs target.refs ptr
    (.valueArray (.number (Int.ofNat (source.globals.length + count + 1)) :: fields)) related.1 oldSeparate
  have newRel := refsRel_writeGlobal relocate source.refs _ newPtr
    (.valueArray (.number (Int.ofNat (source.globals.length + count + 1)) :: fields ++ List.replicate extra (.number 0))) oldRel newSeparate
  refine ⟨newRel, related.2.1, ?_, related.2.2.2⟩
  intro actual actualGlobal
  have same : actual = newPtr := by simpa using Option.some.inj actualGlobal.symm
  subst actual
  refine ⟨newSeparate, oldSize + extra, ?_, ?_⟩
  · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_true, Option.some.injEq, BvlSem.Ref.valueArray.injEq]
    have padding : oldSize - (source.globals.length + 1) + extra =
        count + ((oldSize + extra) - (source.globals.length + count + 1)) := by
      have fieldsLen : fields.length = oldSize - 1 := by simp [fieldsEq]; omega
      omega
    simp [fieldsEq, List.map_append, List.map_replicate, padding, List.append_assoc]
  · have fieldsLen : fields.length = oldSize - 1 := by simp [fieldsEq]; omega
    simp
    omega

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
