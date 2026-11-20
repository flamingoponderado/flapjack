module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation

@[expose] public section

/-! Fixed code lookups derived from the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendCommon
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem stubMembers {width : Nat} [NeZero width] (c : Config) :
    (refByteLocation, 4, refByteCode c) ∈ stubs (width := width) c ∧
    (refArrayLocation, 3, refArrayCode c) ∈ stubs (width := width) c ∧
    (fromListLocation, 4, fromListCode c) ∈ stubs (width := width) c ∧
    (replicateLocation, 5, replicateCode) ∈ stubs (width := width) c ∧
    (anyArithLocation, 4, anyArithCode c) ∈ stubs (width := width) c ∧
    (addLocation, 3, addCode) ∈ stubs (width := width) c ∧
    (subLocation, 3, subCode) ∈ stubs (width := width) c ∧
    (mulLocation, 3, mulCode) ∈ stubs (width := width) c ∧
    (divLocation, 3, divCode) ∈ stubs (width := width) c ∧
    (modLocation, 3, modCode) ∈ stubs (width := width) c := by
  simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
      fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
      replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
      divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
      byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
      installLocation, installCodeLocation, installDataLocation, dummyLocation,
      appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
      unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
namespace StubLookupWitnesses

/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StubLookupWitnesses

/-- The related word state contains the ten fixed stubs required by the compiler. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lookup_RefByte_location"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookupRefByteLocation {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (x : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel c l1 l2 x t none locs) :
    sptLookup refByteLocation t.code = some (4, refByteCode c) ∧
    sptLookup refArrayLocation t.code = some (3, refArrayCode c) ∧
    sptLookup fromListLocation t.code = some (4, fromListCode c) ∧
    sptLookup replicateLocation t.code = some (5, replicateCode) ∧
    sptLookup anyArithLocation t.code = some (4, anyArithCode c) ∧
    sptLookup addLocation t.code = some (3, addCode) ∧
    sptLookup subLocation t.code = some (3, subCode) ∧
    sptLookup mulLocation t.code = some (3, mulCode) ∧
    sptLookup divLocation t.code = some (3, divCode) ∧
    sptLookup modLocation t.code = some (3, modCode) := by
  have code := related.2.2.2.2.1.2.1
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := stubMembers (width := width) c
  exact ⟨code _ h1, code _ h2, code _ h3, code _ h4, code _ h5,
    code _ h6, code _ h7, code _ h8, code _ h9, code _ h10⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
