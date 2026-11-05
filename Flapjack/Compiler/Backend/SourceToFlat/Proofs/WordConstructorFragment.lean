import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordSpaceFragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorFragment

/-! Constructor-aware frontend and word simulation composition. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

/-- The actual BVI-to-data assignment for a nonempty constructor belongs to
the constructor-aware fragment, including its generated space reservation. -/
theorem constructor_iAssign_fragment (dest tag : Nat) (args live env : List Nat)
    (nonempty : args ≠ []) :
    VerifiedWithConstructors (BviToData.iAssign dest (.blockOp (.cons tag)) args live env) := by
  cases args with
  | nil => contradiction
  | cons arg rest =>
    simp only [BviToData.iAssign, DataLang.opRequiresNames, DataSpace.opSpaceReq,
      List.length_cons, Nat.succ_ne_zero, ↓reduceIte]
    exact .seq (.established (.makeSpace _ _)) (.constructor dest tag (arg :: rest) (by simp))

/-- A unary tag-zero BVI constructor function lowers through the actual data
optimizations into the constructor-aware fragment. -/
theorem unaryConstructor_compileExp_fragment :
    VerifiedWithConstructors (BviToData.compileExp 1 (.op (.blockOp (.cons 0)) [.var 0])) := by
  have lowered : BviToData.compileExp 1 (.op (.blockOp (.cons 0)) [.var 0]) =
      .seq (.makeSpace 2 (.ls ())) (.seq (.assign 1 (.blockOp (.cons 0)) [0] none) (.return [1])) := by
    with_unfolding_all rfl
  rw [lowered]
  exact .seq (.established (.makeSpace 2 (.ls ())))
    (.seq (.constructor 1 0 [0] (by simp)) (.established (.established (.ret [1]))))

/-- The emitted word body simulates the constructor-aware data fragment.
This is Flapjack pipeline infrastructure with explicit safety assumptions. -/
theorem configuredConstructorFragmentFunction_simulation {C F : Type} (fuel : Nat)
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
    (fragment : VerifiedWithConstructors body)
    (safe : (DataSem.evaluate body sourceState).1 ≠ some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate body sourceState).2.safeForSpace = true) :
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
  have simulation := verifiedWithConstructors64 word codeLabel l1 l2 body fragment 2 sourceState targetState locs related safe spaceSafe
  simpa [wordBody, outcomesWithSpace64, outOfSpace64, fragmentOutcomesAt64,
    outcomes64, continues64, returns64, timesOut64, raises64] using simulation

/-- The simulation applies to a BVI function emitted by the configured frontend. -/
theorem configuredBviConstructorFragment_simulation {C F : Type} (fuel : Nat)
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
    (fragment : VerifiedWithConstructors (BviToData.compileExp arity body))
    (safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError)))
    (spaceSafe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.safeForSpace = true) :
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
  exact configuredConstructorFragmentFunction_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 (BviToData.compileExp arity body)
    sourceState targetState locs related sourceCode lookup fragment safe spaceSafe

/-- Compose the BVI-to-data simulation with the emitted word body.
This is conditional infrastructure, not whole-program correctness. -/
theorem configuredBviConstructorFragment_fromBvi {C F : Type} (fuel : Nat)
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
    (fragment : VerifiedWithConstructors (BviToData.compileExp arity body))
    (spaceSafe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.safeForSpace = true) :
    ∃ code wordBody dataResult final dataNames next ls localsSize stackMax safe peak,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      DataSem.evaluate (BviToData.compileExp arity body) sourceState =
        (some dataResult, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) ∧
      BviToData.stateRel nextBvi { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak } ∧
      BviToData.correctOutcome bviResult sourceState final env.length next (List.range env.length)
        [] dataNames env true (some dataResult) ls ∧
      bviWordOutcomes64 word l1 l2 bviResult (BviToData.compileExp arity body) wordBody sourceState targetState locs ∧
      ∃ wordResult targetFinal, WordSemStateFiniteExact.evaluate wordBody targetState = (some wordResult, targetFinal) ∧
        ((wordResult ≠ .notEnoughSpace ∧ targetFinal.ffi = nextBvi.ffi) ∨
          (wordResult = .notEnoughSpace ∧ targetFinal.ffi.ioEvents <+: nextBvi.ffi.ioEvents)) := by
  have safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError)) := by
    simpa [envLength] using BviToData.compileExp_notType body env bviState nextBvi bviResult
      sourceState bviRun bviSafe vars fresh bviRelated exceptionJump
  obtain ⟨code, wordBody, wordRun, outputLookup, targetLookup, wordOutcome⟩ :=
    configuredBviConstructorFragment_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 body member sourceState targetState
    locs related sourceCode fragment safe spaceSafe
  obtain ⟨dataResult, final, dataNames, next, ls, localsSize, stackMax, safeFlag, peak,
    dataRun, _, finalRel, outcome⟩ :=
    BviToData.compileExp_of_simulation body env bviState nextBvi bviResult sourceState
      (BviToData.simulationFor_all [body] env bviState) bviRun bviSafe vars fresh bviRelated exceptionJump
  have actualDataRun : DataSem.evaluate (BviToData.compileExp arity body) sourceState =
      (some dataResult, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safeFlag, peakHeapLength := peak }) := by
    simpa [envLength] using dataRun
  have bviWord := bviWordOutcomes64_of_data word l1 l2 bviResult (BviToData.compileExp arity body)
    wordBody sourceState targetState locs dataResult _ actualDataRun outcome.1 outcome.2.1 wordOutcome
  have dataFfi : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.ffi = nextBvi.ffi := by
    rw [actualDataRun]
    exact finalRel.2.2.2.2.2.1.symm
  have observations := bviWordOutcomes64_ffi word l1 l2 bviResult (BviToData.compileExp arity body)
    wordBody sourceState targetState locs nextBvi dataFfi bviWord
  exact ⟨code, wordBody, dataResult, final, dataNames, next, ls, localsSize, stackMax, safeFlag, peak,
    wordRun, outputLookup, targetLookup, actualDataRun, finalRel, outcome, bviWord, observations⟩

end Flapjack.Compiler.Backend.SourceToFlat
