module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! The `Skip` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The `Skip` case retains the complete conclusion of
`data_compile_correct`, including all result and space-failure branches.
Its HOL tag is pending source review of the executable compiler and the
state relation's code and oracle dependencies. The word evaluator carries
the real-model assumption documented in `docs/SOUNDNESS.md` item 8; this
case executes no floating-point instruction. -/
theorem dataCompileCorrect_skip {width : Nat} [NeZero width] {C F : Type}
    (source : DataSem.State C F) (conf : Config) (n l l1 l2 : Nat)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (source1 : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (run : DataSem.evaluate .skip source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l .skip).1 target = (res1, target1) ∧
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
  have sourceEq : res = none ∧ source1 = source := by
    simpa [DataSem.evaluate] using run.symm
  rcases sourceEq with ⟨resEq, sourceEq⟩
  subst res
  subst source1
  have compiled : compileControl (width := width) conf n l .skip = (.skip, l) := by
    have h := compileControl_option (width := width) conf n l .skip
    simpa [compileControl?] using h.symm
  have bound : optionLe target.stackMax source.stackMax := by
    rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bound, _⟩
    exact bound
  refine ⟨target, none, ?_, bound, ?_, ?_⟩
  · simp [compiled, WordSemStateFiniteExact.evaluate]
  · simp
  · simp [related]

end Flapjack.Compiler.Backend.DataToWord.Proofs
