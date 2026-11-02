import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Compiler.Backend.DataToWord.Proofs.Total
import Flapjack.Compiler.Backend.WordBignum.Proofs.GenerateTotal

/-! Totality of the configured 64-bit word-lowering suffix. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack

/-- Once the configured source-to-BVI driver succeeds, its 64-bit word
suffix succeeds for every data configuration. This is Flapjack infrastructure:
it establishes neither source correspondence nor semantic preservation. -/
theorem compileCakeToWord64ConfiguredFuel_succeeds_of_bvi (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (bviRun : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names)) :
    ∃ code, compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, code, names) := by
  obtain ⟨lowered, lowerRun⟩ := DataToWord.compileBviPrograms64_succeeds fuel word bviCode
  obtain ⟨fixed, fixedRun⟩ := DataToWord.fixedStubs64_succeeds word
  obtain ⟨bignum, bignumRun⟩ := WordBignum.generateStubs_succeeds 64 DataToWord.bignumLocation
  exact ⟨fixed ++ bignum ++ lowered, by
    simp only [compileCakeToWord64ConfiguredFuel, bviRun]
    change (do
      let code ← bviCode.mapM fun (name, args, body) => do
        let body ← BviToData.compileExpBounded fuel args body
        let (body, _) ← DataToWord.compileControl? (width := 64) word name 2 body
        pure (name, args + 1, body)
      let fixed ← DataToWord.fixedStubs? word
      let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
      pure (nextSource, nextClosure, nextBvlConfig, fixed ++ bignum ++ code, names)) = _
    rw [lowerRun, fixedRun, bignumRun]
    rfl⟩

end Flapjack.Compiler.Backend.SourceToFlat
