module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! The `Tick` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
namespace reviewedDataCompileCorrect_tickMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_tickMap

/-- The `Tick` case retains the complete conclusion of `data_compile_correct`,
including timeout and space-failure branches. The word evaluator inherits the
real-model assumption documented in `docs/SOUNDNESS.md` item 8. The full HOL
theorem still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_tick {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (run : DataSem.evaluate .tick source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l .tick).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  have clocks : target.clock = source.clock := related.2.1
  have bound : optionLe target.stackMax source.stackMax := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have compiled : compileControl (width := width) conf n l .tick = (.tick, l) := by
    have h := compileControl_option (width := width) conf n l .tick
    simpa [compileControl?] using h.symm
  by_cases zero : source.clock = 0
  · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
        source1 = DataSem.flushState true source := by
      simpa [DataSem.evaluate, zero] using run.symm
    rcases sourceEq with ⟨resEq, stateEq⟩
    subst res
    subst source1
    refine ⟨WordSemStateFiniteExact.flushState true target, some .timeOut, ?_, ?_, ?_, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, clocks, zero]
    · simpa [WordSemStateFiniteExact.flushState, DataSem.flushState] using bound
    · simp
    · simp [WordSemStateFiniteExact.flushState, DataSem.flushState, related.1]
  · have sourceEq : res = none ∧ source1 = DataSem.decClock source := by
      simpa [DataSem.evaluate, zero] using run.symm
    rcases sourceEq with ⟨resEq, stateEq⟩
    subst res
    subst source1
    refine ⟨WordSemStateFiniteExact.decClock target, none, ?_, ?_, ?_, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, clocks, zero]
    · simpa [WordSemStateFiniteExact.decClock, DataSem.decClock] using bound
    · simp
    · have h := stateRel_withClock conf l1 l2 source target none locs (source.clock - 1) related
      simpa [WordSemStateFiniteExact.decClock, DataSem.decClock, clocks] using h
end Flapjack.Compiler.Backend.DataToWord.Proofs
