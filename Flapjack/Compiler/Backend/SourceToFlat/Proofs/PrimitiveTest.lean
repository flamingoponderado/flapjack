import Flapjack.Compiler.Backend.Semantics.FlatSem.Test
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.Equality
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PrimitiveType

/-! Primitive comparison preservation for source-to-flat simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

namespace PrimitiveTestPort
/-- Canonical global finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end PrimitiveTestPort

/-- A successful source primitive test yields the same Boolean for related flat values. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "do_test_lemma"
  (fmap_as_finite_support := [c, tys])]
theorem doTest_related (test : Test) (typ : PrimType) (a b : SemanticPrimitivesHOL.Value)
    (result : Bool) (genv : GlobalEnv) (fa fb : FlatSem.Value)
    (premises : SemanticPrimitivesHOL.doTest test typ a b = .val result ∧
      genvCOk genv.c ∧ ValueRel genv a fa ∧ ValueRel genv b fb) :
    FlatSem.doTest test typ fa fb = .val result := by
  obtain ⟨h, ok, ha, hb⟩ := premises
  cases test with
  | equal =>
    by_cases checks : SemanticPrimitivesHOL.checkType typ a && SemanticPrimitivesHOL.checkType typ b
    · simp only [Bool.and_eq_true] at checks
      have ca : SemanticPrimitivesHOL.checkType typ a = true := checks.1
      have cb : SemanticPrimitivesHOL.checkType typ b = true := checks.2
      have cfa := valueRel_checkType genv typ a fa ⟨ha, ok, ca⟩
      have cfb := valueRel_checkType genv typ b fb ⟨hb, ok, cb⟩
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
