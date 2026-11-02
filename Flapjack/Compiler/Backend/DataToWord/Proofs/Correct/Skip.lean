import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-! The skip case of the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Executing the actual compiled skip preserves the candidate state relation
and both source and target continue. This is one production-backed simulation
case, not yet a port of HOL's complete `data_compile_correct`. -/
theorem skip64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) :
    DataSem.evaluate .skip source = (none, source) ∧
    WordSemStateFiniteExact.evaluate (compileControl64 conf secn label .skip).1 target = (none, target) ∧
    BackendProps.optionLe target.stackMax source.stackMax ∧
    stateRel64 conf l1 l2 source target none locs := by
  refine ⟨?_, ?_, related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, related⟩
  · simp [DataSem.evaluate]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
