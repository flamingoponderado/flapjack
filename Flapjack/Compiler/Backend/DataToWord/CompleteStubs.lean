module

public import Flapjack.Compiler.Backend.DataToWord.Stubs
public import Flapjack.Compiler.Backend.WordBignum.Generate

@[expose] public section

/-! Total executable stub table for data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack Flapjack.Compiler.Backend.BackendCommon

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
/-- Every location in the fixed table has an implementation, for every
configuration and positive word width. This Flapjack-specific fact removes
the option wrapper; it does not establish correspondence with HOL's stubs. -/
theorem fixedStubs_succeeds {width : Nat} [NeZero width] (conf : Config) :
    ∃ stubs, fixedStubs? (width := width) conf = some stubs := by
  cases h : encodeHeader (width := width) conf 0 2 <;> cases hdiv : conf.hasLongdiv <;>
    simp [fixedStubs?, compileConfiguredStub?, compileStub?, h, hdiv,
      fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
      replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
      divLocation, modLocation, compare1Location, compareLocation, equal1Location,
      equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
      byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
      installLocation, installCodeLocation, installDataLocation, dummyLocation,
      appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
      unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]

/-- Assemble the fixed table and generated bignum entries in source order.
This executes on the CakeML compiler path. It is not tagged as HOL's `stubs`
until the fixed bodies and shallow-to-deep bignum generator are source-reviewed. -/
def stubs {width : Nat} [NeZero width] (conf : Config) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  (fixedStubs? conf).get (by
    obtain ⟨result, h⟩ := fixedStubs_succeeds (width := width) conf
    simp [h]) ++
  (WordBignum.generateStubs width bignumLocation).get (by
    simp [WordBignum.generateStubs])

/-- The total table preserves the result of the former option-valued
composition for every configuration and positive word width. -/
theorem stubs_eq_option {width : Nat} [NeZero width] (conf : Config) :
    (do
      let fixed ← fixedStubs? (width := width) conf
      let generated ← WordBignum.generateStubs width bignumLocation
      pure (fixed ++ generated)) = some (stubs conf) := by
  obtain ⟨fixed, hf⟩ := fixedStubs_succeeds (width := width) conf
  simp [stubs, hf, WordBignum.generateStubs]

end Flapjack.Compiler.Backend.DataToWord
