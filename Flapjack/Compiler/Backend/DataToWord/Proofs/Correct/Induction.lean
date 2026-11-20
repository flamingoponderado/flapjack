module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Shared full induction claim for data-to-word compiler correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The complete correctness proposition for one source configuration, packaged
for the recursive cases of evaluator induction. This is Flapjack-specific
proof infrastructure, not a separate HOL declaration. -/
abbrev dataCompileCorrectInduction {width : Nat} [NeZero width] {C F : Type}
    (prog : Flapjack.Compiler.Backend.DataLang.Prog) (source : Flapjack.Compiler.Backend.DataSem.State C F) : Prop :=
  ∀ (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (_run : DataSem.evaluate prog source = (res, source1))
    (_notTypeError : res ≠ some (.err (.abort .typeError)))
    (_related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1),
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l prog).1 target = (res1, target1) ∧
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
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi)

end Flapjack.Compiler.Backend.DataToWord.Proofs
