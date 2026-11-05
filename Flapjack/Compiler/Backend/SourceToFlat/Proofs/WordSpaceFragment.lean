import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordFragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.FragmentSpace

/-! Connecting allocation-capable data fragments to configured word output. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

/-- The actual emitted word body has an ordinary simulation outcome or the
permitted allocation failure. This uses the configured frontend output and
the candidate data-to-word relation; it is not whole-program correctness. -/
theorem configuredSpaceFragmentFunction_simulation {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none)
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
  obtain ⟨code, wordRun, codeRel⟩ := compileCakeToWord64ConfiguredFuel_codeRel_noCallKnown fuel source nextSource
    closure nextClosure bvlConfig nextBvlConfig word declarations bviCode names run calls known
  let wordBody := (compileControl64 word codeLabel 2 body).1
  have outputLookup : sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
    exact codeRel.2.2 codeLabel arity body (by simpa [sourceCode] using sourceLookup)
  have targetLookup : sptLookup codeLabel targetState.code = some (arity + 1, wordBody) :=
    related.2.2.2.2.1.2.2 codeLabel arity body sourceLookup
  refine ⟨code, wordBody, wordRun, outputLookup, targetLookup, ?_⟩
  have simulation := verifiedWithSpace64 word codeLabel l1 l2 body fragment 2 sourceState targetState locs related safe
  simpa [wordBody, outcomesWithSpace64, outOfSpace64, fragmentOutcomesAt64,
    outcomes64, continues64, returns64, timesOut64, raises64] using simulation

end Flapjack.Compiler.Backend.SourceToFlat
