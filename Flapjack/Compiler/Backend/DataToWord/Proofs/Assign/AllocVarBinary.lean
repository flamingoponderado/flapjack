module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVarNary
@[expose] public section

/-! Two-argument variable allocation used by `assign_RefArray`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.BackendProps

namespace AllocVarBinaryWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocVarBinaryWitness

/-- The binary (two-argument) instance of variable allocation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "AllocVar_thm_binary"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocVar_binary {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (a1 a2 : Nat) (names : NumSet) (cut : Spt Flapjack.Compiler.Backend.DataSem.Value)
    (i : Nat) (vv : Flapjack.Compiler.Backend.DataSem.Value)
    (limit : Nat) (q : Option (WordSemResult width)) (result : WordSemStateFiniteExact width C F)
    (related : stateRel conf l1 l2 source target none locs)
    (cutEq : DataSem.cutEnv (sptListInsert [a1, a2] names) source.locals = some cut)
    (readArgs : DataSem.getVars [a1, a2] source.locals = some [.number (i : Int), vv])
    (read : target.getVar 1 = some (.word (BitVec.ofNat width (4 * i))))
    (wordBound : 4 * i < 2 ^ width)
    (run : WordSemStateFiniteExact.evaluate (allocVar conf limit (sptListInsert [a1, a2] names)) target =
      (q, result))
    (limitBound : limit < 2 ^ width / 8) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax ∧
      (conf.gcKind ≠ .none ∧ i < limit ∧ DataSem.noThunksInRefs source.refs →
        source.limits.heapLimit <
          DataSem.sizeOfHeapArgs [.number (i : Int), vv] (cutLocals names source) + (i + 1))) ∧
    (q ≠ some .notEnoughSpace → i < limit ∧
      stateRel conf l1 l2 {source with locals := cut, space := i + 1} result none locs ∧
      result.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      result.code = target.code ∧ result.codeBuffer = target.codeBuffer ∧
      result.dataBuffer = target.dataBuffer ∧ result.compileOracle = target.compileOracle ∧ q = none) :=
  allocVar_nary conf l1 l2 source target locs [a1, a2] names cut [.number (i : Int), vv] i limit q result
    related cutEq readArgs read wordBound run limitBound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
