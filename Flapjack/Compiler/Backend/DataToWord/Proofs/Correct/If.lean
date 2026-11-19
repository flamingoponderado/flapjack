module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BoolLookup

@[expose] public section

/-! The `If` case of the data-to-word evaluator simulation. -/
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

namespace reviewedDataCompileCorrect_ifMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_ifMap

/-- The `If` case retains the complete conclusion of `data_compile_correct`.
Its two hypotheses are precisely the branch-conditioned evaluator induction
hypotheses. The word evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. The full theorem still requires assembly of all cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_if {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (name : Nat) (yes no : Flapjack.Compiler.Backend.DataLang.Prog)
    (ihFalse : ∀ value, DataSem.getVar name source.locals = some value →
      DataSem.isBool true value = false → DataSem.isBool false value = true → dataCompileCorrectInduction (width := width) no source)
    (ihTrue : ∀ value, DataSem.getVar name source.locals = some value →
      DataSem.isBool true value = true → dataCompileCorrectInduction (width := width) yes source)
    (run : DataSem.evaluate (.ifThenElse name yes no) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.ifThenElse name yes no)).1 target = (res1, target1) ∧
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
  have compiled : (compileControl (width := width) conf n l (.ifThenElse name yes no)).1 =
      .ite .equal (adjustVar name) (.imm 18) (compileControl (width := width) conf n l yes).1
        (compileControl (width := width) conf n (compileControl (width := width) conf n l yes).2 no).1 := by
    have h := compileControl_option (width := width) conf n l (.ifThenElse name yes no)
    simp [compileControl?, compileControl_option] at h
    exact congrArg Prod.fst h.symm
  cases sourceRead : DataSem.getVar name source.locals with
  | none =>
    have bad : res = some (.err (.abort .typeError)) := by
      have h := congrArg Prod.fst run
      simpa [DataSem.evaluate, sourceRead, DataSem.typeError] using h.symm
    exact (notTypeError bad).elim
  | some value =>
    obtain ⟨word, wordRead⟩ := stateRel_getVar conf l1 l2 source target none locs name value related sourceRead
    obtain ⟨distinct, trueWord, falseWord⟩ := getVar_isTrueOrFalse conf l1 l2 source target locs name value word
      ⟨related, sourceRead, wordRead⟩
    by_cases htrue : DataSem.isBool true value = true
    · have sourceRun : DataSem.evaluate yes source = (res, source1) := by
        simpa [DataSem.evaluate, sourceRead, htrue] using run
      obtain ⟨target1, res1, targetRun, stackBound, spaceFailure, result⟩ :=
        ihTrue value sourceRead htrue conf n l l1 l2 res source1 target locs sourceRun notTypeError related _depth
      refine ⟨target1, res1, ?_, stackBound, spaceFailure, ?_⟩
      · have wordEq := trueWord htrue
        simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, wordEq,
          WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, targetRun]
      · intro hspace
        have hr := result hspace
        cases res with
        | none => exact hr
        | some r =>
          cases r with
          | val values => exact hr
          | err err =>
            cases err with
            | raise value => exact hr
            | abort err => cases err <;> exact hr
    · by_cases hfalse : DataSem.isBool false value = true
      · have sourceRun : DataSem.evaluate no source = (res, source1) := by
          simpa [DataSem.evaluate, sourceRead, htrue, hfalse] using run
        have notTrue : DataSem.isBool true value = false := by
          cases h : DataSem.isBool true value <;> simp_all
        obtain ⟨target1, res1, targetRun, stackBound, spaceFailure, result⟩ :=
          ihFalse value sourceRead notTrue hfalse conf n (compileControl (width := width) conf n l yes).2 l1 l2 res source1 target locs
            sourceRun notTypeError related _depth
        refine ⟨target1, res1, ?_, stackBound, spaceFailure, ?_⟩
        · have wordEq := falseWord hfalse
          have different : (2 : BitVec width) ≠ 18 := by
            intro equal
            have vals : 2 % 2 ^ width = 18 % 2 ^ width := congrArg BitVec.toNat equal
            exact distinct vals.symm
          have comparison : ((2 : BitVec width) == 18) = false := by
            exact beq_eq_false_iff_ne.mpr different
          change (BitVec.ofNat width 2 == BitVec.ofNat width 18) = false at comparison
          simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, wordEq,
            WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, comparison, targetRun]
        · intro hspace
          have hr := result hspace
          cases res with
          | none => exact hr
          | some r =>
            cases r with
            | val values => exact hr
            | err err =>
              cases err with
              | raise value => exact hr
              | abort err => cases err <;> exact hr
      · have bad : res = some (.err (.abort .typeError)) := by
          have h := congrArg Prod.fst run
          simpa [DataSem.evaluate, sourceRead, htrue, hfalse, DataSem.typeError] using h.symm
        exact (notTypeError bad).elim
end Flapjack.Compiler.Backend.DataToWord.Proofs
