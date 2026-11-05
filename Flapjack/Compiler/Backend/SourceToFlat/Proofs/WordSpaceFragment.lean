import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordFragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.FragmentSpace
import Flapjack.Compiler.Backend.BviToData.Proofs.Simulation

/-! Connecting allocation-capable data fragments to configured word output. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

/-- The actual emitted word body has an ordinary simulation outcome or the
permitted allocation failure, for all closure-optimizer settings. The candidate
data-to-word relation and uncovered instructions remain open, so this is not
whole-program correctness. -/
theorem configuredSpaceFragmentFunction_simulation {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : DataLang.Prog)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (sourceLookup : sptLookup codeLabel sourceState.code = some (arity, body))
    (fragment : VerifiedWithSpace body)
    (safe : (DataSem.evaluate body sourceState).1 ≠ some (.err (.abort .typeError))) :
    ∃ code wordBody,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      (fragmentOutcomesAt64 word l1 l2 body wordBody sourceState targetState locs ∨
        ∃ final, WordSemStateFiniteExact.evaluate wordBody targetState = (some .notEnoughSpace, final) ∧
          BackendProps.optionLe final.stackMax (DataSem.evaluate body sourceState).2.stackMax ∧
          final.ffi.ioEvents <+: (DataSem.evaluate body sourceState).2.ffi.ioEvents ∧
          (word.gcKind ≠ .none → (DataSem.evaluate body sourceState).2.safeForSpace = false)) := by
  obtain ⟨code, wordRun, codeRel⟩ := compileCakeToWord64ConfiguredFuel_codeRel_allSettings fuel source nextSource
    closure nextClosure bvlConfig nextBvlConfig word declarations bviCode names run
  let wordBody := (compileControl64 word codeLabel 2 body).1
  have outputLookup : sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
    exact codeRel.2.2 codeLabel arity body (by simpa [sourceCode] using sourceLookup)
  have targetLookup : sptLookup codeLabel targetState.code = some (arity + 1, wordBody) :=
    related.2.2.2.2.1.2.2 codeLabel arity body sourceLookup
  refine ⟨code, wordBody, wordRun, outputLookup, targetLookup, ?_⟩
  have simulation := verifiedWithSpace64 word codeLabel l1 l2 body fragment 2 sourceState targetState locs related safe
  simpa [wordBody, outcomesWithSpace64, outOfSpace64, fragmentOutcomesAt64,
    outcomes64, continues64, returns64, timesOut64, raises64] using simulation

/-- An entry of the BVI code emitted by the configured frontend is present in
the data code map with its compiled body. Label uniqueness follows from the
actual frontend run, including all closure-optimizer settings. -/
theorem configuredBvi_data_lookup (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode) :
    sptLookup codeLabel (sptFromAList (BviToData.compileProg bviCode)) =
      some (arity, BviToData.compileExp arity body) := by
  have distinct : ((BviToData.compileProg bviCode).map Prod.fst).Nodup := by
    rw [bviToData_labels]
    exact (configured_bvi_labels fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run).1
  have dataMember : (codeLabel, arity, BviToData.compileExp arity body) ∈ BviToData.compileProg bviCode := by
    apply List.mem_map.mpr
    exact ⟨(codeLabel, arity, body), member, rfl⟩
  rw [sptLookup_sptFromAList]
  apply sptAListLookup_eq_of_mem_unique _ _ _ dataMember
  intro other otherMember
  have eq : (codeLabel, other) = (codeLabel, arity, BviToData.compileExp arity body) :=
    List.inj_on_of_nodup_map distinct otherMember dataMember rfl
  exact congrArg Prod.snd eq

/-- The word body emitted for an actual frontend BVI function simulates its
compiled data body, including allocation failure. The verified-fragment,
candidate-state-relation and source-safety conditions remain explicit; this
is Flapjack pipeline infrastructure, not full compiler correctness. -/
theorem configuredBviSpaceFragment_simulation {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (fragment : VerifiedWithSpace (BviToData.compileExp arity body))
    (safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError))) :
    ∃ code wordBody,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      (fragmentOutcomesAt64 word l1 l2 (BviToData.compileExp arity body) wordBody sourceState targetState locs ∨
        ∃ final, WordSemStateFiniteExact.evaluate wordBody targetState = (some .notEnoughSpace, final) ∧
          BackendProps.optionLe final.stackMax (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.stackMax ∧
          final.ffi.ioEvents <+: (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.ffi.ioEvents ∧
          (word.gcKind ≠ .none → (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.safeForSpace = false)) := by
  have lookup : sptLookup codeLabel sourceState.code = some (arity, BviToData.compileExp arity body) := by
    rw [sourceCode]
    exact configuredBvi_data_lookup fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run codeLabel arity body member
  exact configuredSpaceFragmentFunction_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 (BviToData.compileExp arity body)
    sourceState targetState locs related sourceCode lookup fragment safe

/-- A non-type-error BVI evaluation supplies the data-safety premise for the
actual emitted word-body simulation. This connects the two existing Lean-side
pass proofs; their candidate relations, exception premise, verified fragment,
and cross-language correspondence reviews remain explicit. -/
theorem configuredBviSpaceFragment_fromBvi {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (env : List BvlSem.Value) (envLength : env.length = arity)
    (bviState nextBvi : BviSem.BviState C F) (bviResult : BviSem.BviResult)
    (bviRun : BviSem.evaluate [body] env bviState = (bviResult, nextBvi))
    (bviSafe : bviResult ≠ .err (.abort .typeError))
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (vars : DataProps.varCorr env (List.range env.length) (sptMap BviToData.dataToBviValue sourceState.locals))
    (fresh : ∀ k, env.length ≤ k → sptLookup k sourceState.locals = none)
    (bviRelated : BviToData.stateRel bviState sourceState)
    (exceptionJump : BviToData.isException bviResult → DataSem.jumpExc sourceState ≠ none)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (fragment : VerifiedWithSpace (BviToData.compileExp arity body)) :
    ∃ code wordBody,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      (fragmentOutcomesAt64 word l1 l2 (BviToData.compileExp arity body) wordBody sourceState targetState locs ∨
        ∃ final, WordSemStateFiniteExact.evaluate wordBody targetState = (some .notEnoughSpace, final) ∧
          BackendProps.optionLe final.stackMax (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.stackMax ∧
          final.ffi.ioEvents <+: (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.ffi.ioEvents ∧
          (word.gcKind ≠ .none → (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.safeForSpace = false)) := by
  have safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError)) := by
    simpa [envLength] using BviToData.compileExp_notType body env bviState nextBvi bviResult
      sourceState bviRun bviSafe vars fresh bviRelated exceptionJump
  exact configuredBviSpaceFragment_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 body member sourceState targetState
    locs related sourceCode fragment safe

end Flapjack.Compiler.Backend.SourceToFlat
