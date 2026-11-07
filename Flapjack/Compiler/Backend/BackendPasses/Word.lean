import Flapjack.Compiler.Backend.BackendPasses.Data
import Flapjack.Compiler.Backend.PresLang.Word
import Flapjack.Compiler.Backend.SourceToFlat.ToWord

/-! Capture the initial DataLang-to-WordLang stage from
`backend_passesScript.sml`. This follows the executable 64-bit backend path,
including its generated bignum stubs; the subsequent word optimizations and the
complete explorer driver remain to be captured. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString

/-- Capture the original-order WordLang functions and their label names. -/
structure WordStage where
  functions : List (Nat × Nat × WordLangProgHOL (BitVec 64))
  names : Spt MlString

/-- Lower all optimized data functions and prepend the compiler's runtime
stubs. `none` denotes a rejected lowering or unsupported stub configuration. -/
def captureWord64 (config : DataToWord.Config) (data : DataStages) : Option WordStage := do
  let functions ← data.spaced.mapM fun (n, arity, body) => do
    let (body, _) ← DataToWord.compileControl? (width := 64) config n 2 body
    pure (n, arity + 1, body)
  let fixed ← DataToWord.fixedStubs? config
  let bignum ← WordBignum.generateStubs 64 DataToWord.bignumLocation
  pure ⟨fixed ++ bignum ++ functions, data.names⟩

/-- Render the captured WordLang stage with CakeML's original heading. -/
def wordReportBytes (stage : WordStage) : List HolChar :=
  (ofString "# after data_to_word\n\n").explode ++
    PresLang.Word.functionBytes stage.names stage.functions

end Flapjack.Compiler.Backend.BackendPasses
