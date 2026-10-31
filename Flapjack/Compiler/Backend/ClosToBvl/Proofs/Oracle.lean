import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence

/-! Future code and compilation-oracle conditions used by the pass simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosProps Flapjack.Compiler.Backend.BackendProps

/-- The checked program converter produces the same incremental result as the
source-shaped definition. This is Flapjack infrastructure connecting the two
compilation interfaces. -/
theorem compileInc_checked_eq (maxApp : Nat) (program : ClosSem.Program) :
    (let (start, expressions) := extractName program.1
     compileProg? maxApp (chainExps start expressions ++ program.2)) =
      some (compileInc maxApp program) := by
  cases h : extractName program.1 with
  | mk start expressions =>
      simpa [compileInc, h] using
        compileProg_checked_eq_original maxApp (chainExps start expressions ++ program.2)

/-- Accumulate the code installed by the first `n` future oracle entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "nth_code_def"]
def nthCode {C A : Type} (oracle : Nat → C × List (Nat × A)) : Nat → Spt A
  | 0 => .ln
  | n + 1 => sptUnion (sptFromAList (oracle 0).2) (nthCode (fun i => oracle (i + 1)) n)

/-- The compiler and oracle agree with incremental conversion, with fresh
future labels and the source annotations required by closure conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_oracle_inv_def" 1069]
def compileOracleInv {CC OC Result S : Type} (maxApp : Nat) (_sourceCode : S)
    (sourceCompiler : CC → ClosSem.Program → Result)
    (sourceOracle : ClosSem.CompileOracle OC)
    (targetCode : Spt (Nat × Bvl.Exp))
    (targetCompiler : CC → List (Nat × Nat × Bvl.Exp) → Result)
    (targetOracle : BvlSem.CompileOracle OC) : Prop :=
  sourceCompiler = pureCc (compileInc maxApp) targetCompiler ∧
  targetOracle = pureCo (compileInc maxApp) ∘ sourceOracle ∧
  (∀ n, ((targetOracle n).2.map Prod.fst).Nodup) ∧
  (∀ n p, sptMem p (sptUnion targetCode (nthCode targetOracle n)) →
    p ∉ (targetOracle n).2.map Prod.fst) ∧
  ∀ n, everyFnLocationSome (sourceOracle n).2.1 ∧
    everyFnVarsSome (sourceOracle n).2.1 ∧
    (∀ entry ∈ (sourceOracle n).2.2, everyFnLocationSome [entry.2.2]) ∧
    (∀ entry ∈ (sourceOracle n).2.2, everyFnVarsSome [entry.2.2])

end Flapjack.Compiler.Backend.ClosToBvl
