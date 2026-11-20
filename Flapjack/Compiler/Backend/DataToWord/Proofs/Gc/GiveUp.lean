module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocDimword
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLemma
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLocals
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
@[expose] public section

/-! Evaluation of the allocation-failure program. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace GiveUpWitnesses
/-- Canonical finite-map roundtrip for the target state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end GiveUpWitnesses

/-- GiveUp always reports insufficient space and preserves the source FFI. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "evaluate_GiveUp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateGiveUp {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    ∃ result, WordSemStateFiniteExact.evaluate (giveUp (width := width)) target = (some .notEnoughSpace, result) ∧
      result.ffi = source.ffi ∧ target.ffi = source.ffi := by
  have good := related.2.2.2.2.2.2.1
  have allocSize := allocSize_dimword (width := width) good
  have cut : DataSem.cutEnv .ln source.locals = some .ln := by
    have inter : sptInter source.locals (.ln : NumSet) = .ln := by
      cases source.locals <;> simp [sptInter]
    simp [DataSem.cutEnv, inter, sptMkWf]
  cases run : WordSemStateFiniteExact.alloc (-1) (adjustSets (.ln : NumSet)) target with
  | mk q result =>
    have runSize : WordSemStateFiniteExact.alloc (gcAllocSize (2 ^ width)) (adjustSets (.ln : NumSet)) target = (q, result) := by
      simpa [allocSize] using run
    have facts := allocLemma conf l1 l2 source target result locs .ln .ln (2 ^ width) q ⟨related, cut, runSize⟩
    have bad : q = some .notEnoughSpace := by
      by_contra h
      have contradiction := (facts.2 h).2.1
      exact contradiction allocSize
    have ffiEq := (facts.1 bad).1
    have clocks := WordSemStateFiniteExact.alloc_clock (α := Unit) (-1) (adjustSets (.ln : NumSet)) () target q result run
    subst q
    refine ⟨result, ?_, ffiEq, related.1⟩
    simp [giveUp, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.fixClock, sptLookup_sptInsert_same, alloc_locals_insert_one]
    cases result
    simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
