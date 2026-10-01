import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full source map extension, including arbitrary native trees and keys.
Nonphysicality is the source premise; allocation-class membership is not required. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_extend"]
theorem ssaMapOKExtend (next : Nat) (ssa : Spt Nat) (name : Nat)
    (h : ssaMapOK next ssa ∧ ¬ isPhyVar next) :
    ssaMapOK (next + 4) (sptInsert name next ssa) := by
  intro x y hlookup
  by_cases hx : x = name
  · subst x
    rw [sptLookup_sptInsert_same] at hlookup
    cases hlookup
    exact ⟨h.2, by omega⟩
  · rw [sptLookup_sptInsert_ne name x next ssa hx] at hlookup
    obtain ⟨hn, hb⟩ := h.1 x y hlookup
    exact ⟨hn, by omega⟩

end Flapjack.Compiler.Backend.WordAlloc
