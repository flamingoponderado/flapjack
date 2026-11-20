module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number
@[expose] public section

/-! Numeric source locals in the data-to-word state relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace NumberVarWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end NumberVarWitnesses

/-- The low bit of a related number identifies whether it is a bignum. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_get_var_Number_IMP_alt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVar_number_alt {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (k : Nat) (i : Int) (a : WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (sourceRead : DataSem.getVar k source.locals = some (.number i))
    (targetRead : target.getVar (2 * k + 2) = some a) :
    ∃ w : BitVec width, a = .word w ∧ (w.getLsbD 0 = true ↔ ¬ smallInt width i) := by
  have roots := memoryRel_getVar k (holThe source.tstamps) target target.store source.space
    source target.memory
    ([(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    target.mdomain conf target.be (.number i) a (by
      refine ⟨?_, sourceRead, ?_⟩
      · simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      · simpa [adjustVar, Nat.mul_comm] using targetRead)
  exact memoryRel_anyNumberImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain i a
    (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    ⟨related.2.2.2.2.2.2.1, by simpa using roots⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
