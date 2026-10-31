import Flapjack.Compiler.Backend.BvlToBvi.Proofs.NoMutcons
import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation

/-! Production BVL-to-BVI and tail-recursion handoff into TMC code relations. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- The production TMC pass installs code and namespace relations after
the preceding passes, and leaves its resulting worker labels fresh. This is
Flapjack pipeline infrastructure rather than a standalone HOL theorem. -/
theorem lowered_tailrec_tmc_code_and_namespace
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered beforeTmc afterTmc : List (Nat × Nat × Bvi.Exp))
    (tailLast tmcLast : Nat) (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (tailLast, beforeTmc))
    (tmcRun : BviTmc.compileProgFuel fuel true (bvlNumStubs + 3) beforeTmc = some (tmcLast, afterTmc)) :
    BviTmc.codeRel (sptFromAList beforeTmc) (sptFromAList afterTmc) ∧
    BviTmc.namespaceRel (sptFromAList beforeTmc) (sptFromAList afterTmc) ∧
    (afterTmc.map Prod.fst).Nodup ∧ ∀ entry ∈ afterTmc, BviTmc.freeNames tmcLast entry.1 := by
  have condition := lowered_tailrec_tmc_inputCondition_complete fuel optFuel start counter targetStart targetCounter
    enabled program lowered beforeTmc tailLast distinct lowerRun tailRun
  have sourceRun : BviTmc.compileEachSource (bvlNumStubs + 3) beforeTmc = (tmcLast, afterTmc) := by
    have equal := (BviTmc.compileEachFuel_eq_source fuel (bvlNumStubs + 3) beforeTmc).symm.trans
      (by simpa [BviTmc.compileProgFuel] using tmcRun)
    exact Option.some.inj equal
  exact ⟨BviTmc.compileEachSource_codeRel _ _ _ _ sourceRun condition.2.2.1 condition.1 condition.2.1,
    BviTmc.compileEachSource_namespaceRel _ _ _ _ sourceRun condition.2.2.2.2.2 condition.2.2.2.2.1
      condition.2.2.2.1,
    BviTmc.compileEachSource_distinct_and_free _ _ _ _ sourceRun condition.2.2.1 condition.1⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
