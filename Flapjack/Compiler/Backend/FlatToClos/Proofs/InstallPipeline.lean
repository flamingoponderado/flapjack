import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.ClosInterp.Proofs.StateRelation

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

/-- A production callback relation supplies the intermediate callback
required by the flat-to-closure simulation. -/
theorem production_installConfigRel {C : Type} (source : FlatSem.InstallConfig C)
    (compiler : ClosSem.Compiler C)
    (safe : ∀ index, FlatProps.noMatDecs (source.compileOracle index).2 = true)
    (production : source.compile = pureCc incCompileDecs compiler) :
    installConfigRel source (pureCo (incCompileDecsProofSide (α := Nat × Nat × ClosLang.Exp)) ∘ source.compileOracle)
      (pureCc ClosInterp.insertProgram compiler) := by
  refine ⟨safe, rfl, ?_⟩
  have factor := (incCompileDecs_intro (P := Unit) (fun (_ : Unit) => ((), [])) compiler).2
  exact production.trans factor.symm


end Flapjack.Compiler.Backend.FlatToClos
