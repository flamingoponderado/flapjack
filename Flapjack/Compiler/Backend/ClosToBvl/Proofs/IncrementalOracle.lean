module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Compiler.Backend.BackendProps.Pure

@[expose] public section

/-! Oracle invariants for incremental closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open BackendProps

/-- Compiling each oracle entry preserves ordering of its required addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_inc_monotonic"]
theorem compileInc_monotonic {C : Type} (maxApp : Nat) (initial : Set Nat)
    (oracle : Nat → C × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))) :
    oracleMonotonic
      (fun entry : C × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) =>
        {x | x ∈ (reqCompileIncAddrs [] entry.2).map (numStubs maxApp + ·)})
      (· < ·) initial oracle →
    oracleMonotonic (fun entry : C × List (Nat × Nat × Bvl.Exp) => {x | x ∈ entry.2.map Prod.fst})
      (· < ·) initial (pureCo (compileInc maxApp) ∘ oracle) := by
  intro ordered
  apply oracleMonotonic_subset initial initial
    (fun entry : C × List (Nat × Nat × Bvl.Exp) => {x | x ∈ entry.2.map Prod.fst}) (pureCo (compileInc maxApp) ∘ oracle)
    (fun entry : C × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) =>
        {x | x ∈ (reqCompileIncAddrs [] entry.2).map (numStubs maxApp + ·)}) oracle (· < ·)
    ?_ ordered
  constructor
  · exact Set.Subset.rfl
  · intro n
    simpa [pureCo, Function.comp_def] using (compileInc_reqAddrs (oracle n).2 maxApp).2

end Flapjack.Compiler.Backend.ClosToBvl
