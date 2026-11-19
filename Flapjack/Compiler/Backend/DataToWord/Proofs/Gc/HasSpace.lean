module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space

@[expose] public section

/-! Source allocation-space preservation for related states. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
namespace HasSpaceWitnesses
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end HasSpaceWitnesses

/-- A successful target space check permits the same source allocation allowance. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "has_space_state_rel"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem hasSpace_stateRel {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (k : Nat)
    (h : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize (width := width) k)) t = some true ∧
      stateRel c l1 l2 s t none locs) :
    stateRel c l1 l2 {s with space := k} t none locs := by
  obtain ⟨hasSpace, related⟩ := h
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  obtain ⟨next, trigger, available, nextStore, triggerStore, gap, _, maxMem, bound⟩ :=
    memoryRel_spaceMax c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _ hmem
  have fits : (gcAllocSize k : BitVec width) ≤ wordSemBytesInWord * BitVec.ofNat width available := by
    apply BitVec.le_def.mpr
    have availableSpace : (gcAllocSize k : BitVec width).toNat ≤ (trigger - next).toNat := by
      simpa [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, nextStore, triggerStore] using hasSpace
    rw [gap] at availableSpace
    exact availableSpace
  have kBound : k ≤ available := gcAllocSize_le_imp k available fits (by simpa [Nat.mul_comm] using bound hgood) hgood
  have newMem := memoryRel_lessSpace c t.be (holThe s.tstamps) s.refs available k t.store t.memory t.mdomain _
    ⟨maxMem, kBound⟩
  exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal, hzero, hpresent,
    hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, newMem⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
