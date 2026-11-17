module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosInterp.Proofs.StateRelation

@[expose] public section

/-! Composition of flat-to-closure compilation with interpreter insertion.
These identities connect the actual compiler callbacks; the semantic
correctness of interpreter insertion remains a separate proof obligation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendProps

/-- Interpreter insertion composes with incremental oracle and compiler paths. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "inc_compile_decs_intro"]
theorem incCompileDecs_intro {I O P C R Q : Type}
    (f : I → O × List FlatLang.Exp) (cc : C → (List ClosLang.Exp × List Q) → R) :
    (pureCo (Prod.map ClosInterp.insertInterp (id : List P → List P)) ∘
      pureCo (incCompileDecsProofSide (α := P)) ∘ f = pureCo (incCompileDecs (α := P)) ∘ f) ∧
    (pureCc (incCompileDecsProofSide (α := Q))
        (pureCc (Prod.map ClosInterp.insertInterp (id : List Q → List Q)) cc) =
      pureCc (incCompileDecs (α := Q)) cc) := by
  constructor
  · funext i
    cases f i
    rfl
  · rfl

end Flapjack.Compiler.Backend.FlatToClos
