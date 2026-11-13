module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramProperties
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.NoMutcons

@[expose] public section

/-! Conditions for future programs in the BVL-to-BVI pass chain. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend

private theorem inlineInc_names (limit : Nat) (split : Bool) (cut : Nat)
    (cache : Spt (Nat × Bvl.Exp)) (prog : List (Nat × Nat × Bvl.Exp)) :
    ((BvlInline.compileInc limit split cut cache prog).2.map Prod.fst) = prog.map Prod.fst := by
  cases h : BvlInline.tickCompileProg limit cache prog with
  | mk finalCache output =>
    have names := BvlInline.mapFstTickInlineAll limit cache prog
    change (BvlInline.tickCompileProg limit cache prog).2.map Prod.fst = prog.map Prod.fst at names
    simp only [BvlInline.compileInc, h]
    rw [BvlInline.Proofs.mapFstMapOptimise]
    simpa only [h, Prod.snd] using names

private theorem incTail_tmc_condition (counter next2 next3 : Nat) (enabled : Bool)
    (prog : List (Nat × Nat × Bvl.Exp)) (distinct : (prog.map Prod.fst).Nodup)
    (bound2 : bvlNumStubs ≤ next2) (worker2 : BviTailrec.inWorkerNamespace next2)
    (bound3 : bvlNumStubs ≤ next3) (worker3 : BviTmc.inWorkerNamespace next3) :
    BviTmc.inputCondition next3
      ((BviTailrec.compileProgSource enabled next2 (compileIncSource counter prog).2).2) := by
  let lower := (compileIncSource counter prog).2
  let result := BviTailrec.compileProgSource enabled next2 lower
  have cond : BviTailrec.inputCondition next2 lower :=
    compileIncSource_tailrec_inputCondition counter next2 prog distinct bound2 worker2
  have outside : ∀ name ∈ lower.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name := by
    intro name member _
    exact compileIncSource_outside_tmc_namespace counter prog name member
  have lowerSafe : ∀ entry ∈ lower, BviTmc.noMutcons entry.2.2 :=
    compileIncSource_noMutcons counter (compileIncSource counter prog).1 prog lower (Prod.eta _).symm
  have run : BviTailrec.compileProgFuel 0 enabled next2 lower = some (result.1, result.2) := by
    simpa [result] using BviTailrec.compileProgFuel_eq_source 0 enabled next2 lower
  have safe := tailrec_compileProgFuel_noMutcons 0 enabled next2 result.1 lower result.2 run lowerSafe
  exact tailrec_output_tmc_inputCondition 0 enabled next2 result.1 next3 lower result.2 cond outside safe bound3 worker3 run

private theorem loweredTailrecOracle_tmcCondition {C : Type} (enabled : Bool)
    (oracle : Nat → (Nat × (Nat × (Nat × C))) × List (Nat × Nat × Bvl.Exp))
    (distinct : ∀ i, ((oracle i).2.map Prod.fst).Nodup)
    (bounds2 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.1)
    (worker2 : ∀ i, BviTailrec.inWorkerNamespace (oracle i).1.2.1)
    (bounds3 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.2.1)
    (worker3 : ∀ i, BviTmc.inWorkerNamespace (oracle i).1.2.2.1) :
    ∀ i, BviTmc.inputCondition
      ((BackendProps.stateCo (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCo compileIncSource oracle) i).1.1)
      ((BackendProps.stateCo (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCo compileIncSource oracle) i).2) := by
  intro i
  simpa [BackendProps.stateCo] using incTail_tmc_condition (oracle i).1.1
    (oracle i).1.2.1 (oracle i).1.2.2.1 enabled (oracle i).2 (distinct i)
    (bounds2 i) (worker2 i) (bounds3 i) (worker3 i)

/-- Future programs satisfy the TMC input condition after inlining, lowering,
and tail-recursion. This is Flapjack infrastructure for the oracle obligation
in the source whole-pipeline correctness proof, which discharges it inline. -/
theorem fullOracle_tmcCondition {C : Type} (limit : Nat) (split : Bool) (cut : Nat) (enabled : Bool)
    (oracle : Nat → (Spt (Nat × Bvl.Exp) × (Nat × (Nat × (Nat × C)))) × List (Nat × Nat × Bvl.Exp))
    (distinct : ∀ i, ((oracle i).2.map Prod.fst).Nodup)
    (bounds2 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.2.1)
    (worker2 : ∀ i, BviTailrec.inWorkerNamespace (oracle i).1.2.2.1)
    (bounds3 : ∀ i, bvlNumStubs ≤ (oracle i).1.2.2.2.1)
    (worker3 : ∀ i, BviTmc.inWorkerNamespace (oracle i).1.2.2.2.1) :
    ∀ i, BviTmc.inputCondition
      ((BackendProps.stateCo (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCo compileIncSource
          (BackendProps.stateCo (BvlInline.compileInc limit split cut) oracle)) i).1.1)
      ((BackendProps.stateCo (BviTailrec.compileProgSource enabled)
        (BackendProps.stateCo compileIncSource
          (BackendProps.stateCo (BvlInline.compileInc limit split cut) oracle)) i).2) := by
  apply loweredTailrecOracle_tmcCondition enabled
    (BackendProps.stateCo (BvlInline.compileInc limit split cut) oracle)
  · intro i
    simpa [BackendProps.stateCo, inlineInc_names] using distinct i
  · simpa [BackendProps.stateCo] using bounds2
  · simpa [BackendProps.stateCo] using worker2
  · simpa [BackendProps.stateCo] using bounds3
  · simpa [BackendProps.stateCo] using worker3

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
