module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values

@[expose] public section

/-! Heap and state-relation facts used by the data-to-word bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace StateRelWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end StateRelWitnesses

/-- A bignum found after an unused heap block lies beyond that block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "heap_lookup_Unused_Bignum"
  (words_as_type_indexed_bitvec)]
theorem heapLookup_unused_bignum {width : Nat} [NeZero width] {α : Type} (a k : Nat) (j : Int)
    (hb : List (HeapElement α (HeapTag × List (WordLocW width)))) :
    heapLookup a (.unused k :: hb) = some (bignumRep j) ↔
      k + 1 ≤ a ∧ heapLookup (a - (k + 1)) hb = some (bignumRep j) := by
  simp only [heapLookup, elLength]
  by_cases zero : a = 0
  · subst zero
    simp [bignumRep]
  · by_cases small : a < k + 1
    · simp [zero, small]
    · simp [zero, small]
      omega

/-- A single extra root may be replaced by a small number and its encoding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "state_rel_Number_small_int"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_number_smallInt {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (r1 r2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (x : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width) (locs : List (Nat × Nat)) (i : Int) :
    stateRel c r1 r2 s t (some [x]) locs ∧ smallInt width i →
      stateRel c r1 r2 s t (some [(.number i, .word (smallnum i : BitVec width))]) locs := by
  rintro ⟨related, small⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, good, h8, h9, h10, _, h12, h13, h14, h15, h16, h17, h18, h19, mem⟩ :=
    related
  refine ⟨h1, h2, h3, h4, h5, h6, good, h8, h9, h10, by simp, h12, h13, h14, h15, h16, h17, h18, h19, ?_⟩
  have rest := memoryRel_rearrange c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _
    (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
      [(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    (by intro pair member; simp only [Option.getD_some, List.mem_append, List.mem_cons] at member ⊢; tauto)
    mem
  simpa using impMemoryRel_number c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain _ i
    ⟨good, small, rest⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
