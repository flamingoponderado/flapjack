import Flapjack.Compiler.Backend.Semantics.FlatSem.Test
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- A successful source primitive test yields the same Boolean for related
flat values. This is infrastructure over the factored relation, whose full
HOL correspondence remains open. -/
theorem doTest_related (genv : GlobalEnv) (ok : genvCOk genv.c)
    (test : Test) (typ : PrimType) (a b : SemanticPrimitivesHOL.Value)
    (fa fb : FlatSem.Value) (result : Bool)
    (ha : ValueRel genv a fa) (hb : ValueRel genv b fb)
    (h : SemanticPrimitivesHOL.doTest test typ a b = .val result) :
    FlatSem.doTest test typ fa fb = .val result := by
  cases test with
  | equal =>
    by_cases checks : SemanticPrimitivesHOL.checkType typ a && SemanticPrimitivesHOL.checkType typ b
    · simp only [Bool.and_eq_true] at checks
      have ca : SemanticPrimitivesHOL.checkType typ a = true := checks.1
      have cb : SemanticPrimitivesHOL.checkType typ b = true := checks.2
      have cfa := valueRel_checkType genv ok typ a fa ha ca
      have cfb := valueRel_checkType genv ok typ b fb hb cb
      have heq := equality_preserved genv ok a b fa fb ha hb
      cases typ <;> simp_all [SemanticPrimitivesHOL.doTest, FlatSem.doTest]
      cases ha <;> cases hb <;> simp_all [SemanticPrimitivesHOL.checkType, FlatSem.checkType]
      rename_i lit1 lit2
      cases lit1 <;> cases lit2 <;> simp_all
    · simp [SemanticPrimitivesHOL.doTest, checks] at h
  | compare op =>
    simp only [SemanticPrimitivesHOL.doTest] at h
    split at h
    all_goals try contradiction
    all_goals cases ha
    all_goals cases hb
    all_goals simpa [FlatSem.doTest] using h
  | altCompare op =>
    simp only [SemanticPrimitivesHOL.doTest] at h
    split at h
    all_goals try contradiction
    all_goals cases ha
    all_goals cases hb
    all_goals simpa [FlatSem.doTest] using h
end Flapjack.Compiler.Backend.SourceToFlat
