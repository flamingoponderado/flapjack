module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 2279-2284: the closure-to-BVL syntax-oracle
precondition ignores the output configuration's `start` field. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend.ClosToBvl

/-- Exact HOL `syntax_oracle_ok_start` (`backendProofScript.sml:2279-2284`).
`c' with start updated_by f` is the record update applying `f` to the old
field; boolean equality is `↔`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "syntax_oracle_ok_start"]
theorem syntaxOracleOk_start {α : Type} (c c' : ClosToBvl.Config) (f : Nat → Nat)
    (es : List ClosLang.Exp)
    (co : Nat → (Nat × Spt ClosKnown.ValApprox × NumSet × α) × ClosSem.Program) :
    syntaxOracleOkCommon c { c' with start := f c'.start } es co ↔
      syntaxOracleOkCommon c c' es co := Iff.rfl

end Flapjack.Compiler.Backend.BackendProof
