module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot

@[expose] public section

/-! Boolean local values in the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.BackendCommon

namespace boolLookupMap
/-- Canonical target-state roundtrip for the local lookup theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end boolLookupMap

/-- Related Boolean locals have the original distinct immediate encodings. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_var_T_OR_F"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_trueOrFalse {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (n : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVar n source.locals = some value ∧
      WordSemStateFiniteExact.getVar (adjustVar n) target = some word) :
    18 % 2 ^ width ≠ 2 % 2 ^ width ∧
      (value = DataSem.boolValue true → word = .word 18) ∧
      (value = DataSem.boolValue false → word = .word 2) := by
  obtain ⟨related, sourceRead, targetRead⟩ := premises
  have good := related.2.2.2.2.2.2.1
  let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
  let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have heap := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have roots := memoryRel_lookupVars conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain source.locals target rest [n] [value] [word] (by
      refine ⟨?_, ?_, ?_⟩
      · simpa [locals, rest] using heap
      · simp [DataSem.getVars, sourceRead]
      · simp [WordSemStateFiniteExact.getVars, targetRead])
  refine ⟨?_, ?_, ?_⟩
  · rcases good with h | h <;> subst width <;> decide
  · intro eq
    subst value
    have encoded := boolBlock_word conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain 0 1 word (locals ++ rest)
      (by simpa [locals, DataSem.boolValue, boolToTag, trueTag] using roots) good
    rcases good with h | h <;> subst width <;> simpa using encoded
  · intro eq
    subst value
    have encoded := boolBlock_word conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain 0 0 word (locals ++ rest)
      (by simpa [locals, DataSem.boolValue, boolToTag, falseTag] using roots) good
    simpa using encoded

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
