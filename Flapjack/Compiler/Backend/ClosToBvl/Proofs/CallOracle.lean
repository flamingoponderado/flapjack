module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SyntaxOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.NumberOracle
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.KnownAddresses
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallAddresses
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MtiInvariants

@[expose] public section

/-! Oracle ordering after closure preprocessing passes. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps BackendProps

/-- The call-pass oracle generates code labels in increasing order above the initial counter. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "syntax_oracle_ok_call_FST_monotonic"]
theorem syntaxOracleOk_callFst_monotonic {α : Type} (c c' : Config) (es : List ClosLang.Exp)
    (co : Nat → (Nat × Spt ClosKnown.ValApprox × NumSet × α) × ClosSem.Program)
    (prog : List (Nat × Nat × ClosLang.Exp))
    (h : syntaxOracleOkCommon c c' es co ∧ compileCommon c es = (c', prog)) :
    oracleMonotonic
      (fun entry : α × ClosSem.Program => {x | x ∈ entry.2.2.map Prod.fst})
      (· < ·) {x | x < (co 0).1.1}
      (stateCo (ClosCall.condCallCompileInc c.doCall)
        (ClosKnown.knownCo c.knownConf
          (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
            (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)))) := by
  let mco := pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co
  let nco := stateCo (ClosNumber.ignoreTable ClosNumber.compileInc) mco
  let kco := ClosKnown.knownCo c.knownConf nco
  let aco := stateCo (ClosCall.condCallCompileInc c.doCall) kco
  have horacle := h.1
  simp only [syntaxOracleOkCommon] at horacle
  have empty : ∀ i, (mco i).2.2 = [] := by
    intro i
    have h := horacle.1 i
    cases hen : c.doMti <;>
      simp [mco, pureCo, Function.comp_def, ClosMti.condCompileInc, ClosMti.compileInc, hen, h]
  have state : isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc) mco := by
    exact horacle.2.2.2.2.2.2.2.2
  have initial : (mco 0).1.1 = (co 0).1.1 := rfl
  have orderedN := renumberCodeLocs_monotonic_req mco {x | x < (co 0).1.1} 0
    ⟨state, by simp [initial], empty⟩
  have extractN : ∀ i, canExtract (nco i).2.1 := by
    intro i
    exact (numberCompileInc_req (mco i).1.1 (mco i).2 (empty i)).2.2
  have extractK : ∀ i, canExtract (kco i).2.1 := by
    intro i
    exact (knownCo_req nco i c.knownConf (extractN i)).2.1
  have orderedK : oracleMonotonic
      (fun entry : (NumSet × α) × ClosSem.Program =>
        {x | x ∈ reqCompileIncAddrs [Nat.succ] entry.2})
      (· < ·) {x | x < (co 0).1.1} kco := by
    apply oracleMonotonic_subset _ _ _ kco _ nco (· < ·) ?_ orderedN
    refine ⟨Set.Subset.rfl, ?_⟩
    intro i x hx
    have sub := (knownCo_req nco i c.knownConf (extractN i)).2.2 hx
    simpa using sub
  have orderedA : oracleMonotonic
      (fun entry : α × ClosSem.Program => {x | x ∈ reqCompileIncAddrs [] entry.2})
      (· < ·) {x | x < (co 0).1.1} aco := by
    apply oracleMonotonic_subset _ _ _ aco _ kco (· < ·) ?_ orderedK
    refine ⟨Set.Subset.rfl, ?_⟩
    intro i x hx
    exact (condCallCompileInc_req (kco i).2 c.doCall (kco i).1.1 (extractK i)).2.2 hx
  apply oracleMonotonic_subset _ _ _ aco _ aco (· < ·) ?_ orderedA
  refine ⟨Set.Subset.rfl, ?_⟩
  intro i x hx
  simp only [reqCompileIncAddrs, List.map_nil, List.flatten_nil, List.append_nil,
    List.mem_append]
  exact Or.inl (Or.inr hx)

end Flapjack.Compiler.Backend.ClosToBvl
