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

/-- A pointwise reduction of required addresses preserves oracle ordering,
even when the two oracles carry different configurations and metadata. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "subset_req_orac_to_oracle"]
theorem subsetReqOrac_to_oracle {C₁ C₂ M₁ M₂ L : Type}
    (extra₂ : List (Nat → Nat)) (f : Nat → L) (relation : L → L → Prop) (initial : Set L)
    (oracle₁ : Nat → C₁ × (List ClosLang.Exp × List (Nat × M₁ × ClosLang.Exp)))
    (oracle₂ : Nat → C₂ × (List ClosLang.Exp × List (Nat × M₂ × ClosLang.Exp)))
    (extra₁ : List (Nat → Nat)) :
    ((∀ n, {x | x ∈ reqCompileIncAddrs extra₂ (oracle₂ n).2} ⊆
      {x | x ∈ reqCompileIncAddrs extra₁ (oracle₁ n).2}) ∧
      oracleMonotonic
        (fun e : C₁ × (List ClosLang.Exp × List (Nat × M₁ × ClosLang.Exp)) =>
          {x | x ∈ (reqCompileIncAddrs extra₁ e.2).map f}) relation initial oracle₁) →
    oracleMonotonic
      (fun e : C₂ × (List ClosLang.Exp × List (Nat × M₂ × ClosLang.Exp)) =>
        {x | x ∈ (reqCompileIncAddrs extra₂ e.2).map f}) relation initial oracle₂ := by
  intro h
  apply oracleMonotonic_subset initial initial
    (fun e : C₂ × (List ClosLang.Exp × List (Nat × M₂ × ClosLang.Exp)) =>
      {x | x ∈ (reqCompileIncAddrs extra₂ e.2).map f}) oracle₂
    (fun e : C₁ × (List ClosLang.Exp × List (Nat × M₁ × ClosLang.Exp)) =>
      {x | x ∈ (reqCompileIncAddrs extra₁ e.2).map f}) oracle₁ relation ?_ h.2
  constructor
  · exact Set.Subset.rfl
  · intro n x member
    obtain ⟨a, mem, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨a, h.1 n mem, rfl⟩

end Flapjack.Compiler.Backend.ClosToBvl
