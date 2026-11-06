import Flapjack.Compiler.Backend.ClosCall.Proofs.ApplicationSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateControlWellformed
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecursiveInvariant
import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateForce
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

/-! Direct-call simulation of ordinary primitive operations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps SemanticPrimitivesHOL SemanticPrimitivesProps

/-- The environment relation for a primitive expression covers its arguments. -/
theorem envRelFuel_op_args {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {sourceEnv targetEnv : List ClosSem.Value}
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (related : EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 [(0, .op trace op args)]) :
    EnvRelFuel fuel g allowed code sourceEnv targetEnv 0 (args.map (0, ·)) := by
  apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
  have h := (envRelFuel_iff _ _ _ _ _ _ _ _).mp related
  unfold envRel at h ⊢
  by_cases same : sourceEnv.length = targetEnv.length
  · simpa [same] using h
  simp only [same, ↓reduceIte] at h ⊢
  intro x ⟨item, member, free⟩
  obtain ⟨expr, exprMember, rfl⟩ := List.mem_map.mp member
  apply h x
  refine ⟨(0, .op trace op args), by simp, ?_⟩
  simp only [Nat.zero_add, ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false] at free ⊢
  exact freeVars_of_mem x expr args exprMember free

end Flapjack.Compiler.Backend.ClosCall
