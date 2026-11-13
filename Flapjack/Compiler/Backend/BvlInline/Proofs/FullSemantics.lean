module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpSemantics
public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProductionSemantics
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile

@[expose] public section


/-! Production correspondence and behavior for the complete BVL optimizer. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Compose the source callbacks for inlining, tick removal, and let optimization. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "bvl_inline_cc_def"]
def bvlInlineCc {C A B D : Type} (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (compiler : C → List (Nat × Nat × Bvl.Exp) → Option (A × B × D)) :=
  inCc limit (removeTicksCc (letOpCompiler splitSeq cutSize compiler))

/-- Compose the source oracle transformations for the full BVL inlining pass. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "bvl_inline_co_def"]
def bvlInlineCo {I C : Type} (limit : Nat) (splitSeq : Bool) (cutSize : Nat)
    (oracle : I → (Spt (Nat × Bvl.Exp) × C) × List (Nat × Nat × Bvl.Exp)) :=
  letOpOracle splitSeq cutSize (removeTicksCo ∘ inCo limit oracle)

/-- The executed program optimizer returns the total inlining, tick-removal,
let-operation, and handler transformations. -/
theorem compileProgFuel_eq (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) :
    compileProgFuel fuel inlineLimit cutSize splitSeq program =
      let inlined := tickCompileProg inlineLimit .ln program
      let unticked := inlined.2.map fun (name, arity, body) => (name, arity, removeTicksSing body)
      some (inlined.1, unticked.map fun (name, arity, body) =>
        (name, arity, letOpTransform splitSeq cutSize arity body)) := by
  rw [compileProgFuel, compileIncFuel_eq_compileInc]
  simp [compileInc, optimise, letOpTransform, List.map_map,
    Function.comp_def]


end Flapjack.Compiler.Backend.BvlInline.Proofs
