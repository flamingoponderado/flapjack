module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcState

@[expose] public section

/-! The `Raise` case of the data-to-word evaluator simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
namespace reviewedDataCompileCorrect_raiseMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_raiseMap

/-- The `Raise` case retains the complete conclusion of `data_compile_correct`.
The word evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. The full theorem still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_raise {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (name : Nat)
    (run : DataSem.evaluate (.raise name) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.raise name)).1 target = (res1, target1) ∧
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
  have compiled : compileControl (width := width) conf n l (.raise name) =
      (.raise (adjustVar name), l) := by
    have h := compileControl_option (width := width) conf n l (.raise name)
    simpa [compileControl?] using h.symm
  cases sourceRead : DataSem.getVar name source.locals with
  | none =>
    have bad : res = some (.err (.abort .typeError)) := by
      have h := congrArg Prod.fst run
      simpa [DataSem.evaluate, sourceRead, DataSem.typeError] using h.symm
    exact (notTypeError bad).elim
  | some value =>
    cases sourceJump : DataSem.jumpExc source with
    | none =>
      have bad : res = some (.err (.abort .typeError)) := by
        have h := congrArg Prod.fst run
        simpa [DataSem.evaluate, sourceRead, sourceJump, DataSem.typeError] using h.symm
      exact (notTypeError bad).elim
    | some source' =>
      have sourceEq : res = some (.err (.raise value)) ∧ source1 = source' := by
        simpa [DataSem.evaluate, sourceRead, sourceJump] using run.symm
      rcases sourceEq with ⟨resEq, stateEq⟩
      subst res
      subst source1
      obtain ⟨word, wordRead⟩ := stateRel_getVar conf l1 l2 source target none locs name value related sourceRead
      obtain ⟨target', d1, d2, l5, l6, rest, targetJump, suffix, restored⟩ :=
        stateRel_jumpExc conf l1 l2 source source' target locs name value word
          ⟨related, sourceRead, wordRead, sourceJump⟩
      have relZero := restored 0
      have sameFfi : target'.ffi = source'.ffi := by
        simpa [DataSem.setVar, WordSemStateFiniteExact.setVar] using relZero.1
      have bound : optionLe target'.stackMax source'.stackMax := by
        have h := relZero.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simpa [DataSem.setVar, WordSemStateFiniteExact.setVar] using h
      refine ⟨target', some (.exception (.loc d1 d2) word), ?_, bound, ?_, ?_⟩
      · simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, targetJump]
      · simp
      · intro _
        refine ⟨sameFfi, word, l5, l6, rest, ?_, ?_⟩
        · simp [mkLoc, targetJump]
        · intro _
          exact ⟨suffix, restored⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs
