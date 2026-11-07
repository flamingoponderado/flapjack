import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows

/-! Pattern-row safety under the complete source-to-flat invariant. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant

namespace PatternRowsInvariantPort
/-- Canonical global finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end PatternRowsInvariantPort

/-- Matchable source rows cannot become a flat pattern type error. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "can_pmatch_all_IMP_pmatch_rows"
  (fmap_as_finite_support := [c, tys])]
theorem canPmatchAll_implies_pmatchRows {C F : Type} [Nonempty C]
    (env : SemEnv Value) (st : State F) (pes : List (Pat × AstHOL.Exp)) (v : Value)
    (interp : Option (Value → Option (Config × C))) (g : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (flat : FlatSem.State C F)
    (compMap : Environment) (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (v' : FlatSem.Value) (trace : List VarN) (traces : List Tra)
    (premises : canPmatchAll env.c st.refs (pes.map Prod.fst) v = true ∧
      factoredInvariant interp g gen genv idxs st flat ∧
      FactoredEnvAllRel genv compMap env flatEnv locals ∧ ValueRel genv v v') :
    FlatSem.pmatchRows (compilePes trace { compMap with v := bindLocals traces locals compMap.v } pes)
      flat v' ≠ .typeError := by
  obtain ⟨can, invariant, ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localRel⟩, values⟩ := premises
  have envInv : GlobalEnvInv genv compMap (fun _ => True) env := by
    subst env
    subst sourceLocal
    cases globals with
    | intro _ _ _ globalValues globalConstructors =>
      apply GlobalEnvInv.intro
      · intro id val notShadowed lookup
        cases id with
        | short name => exact (notShadowed ⟨name, trivial, rfl⟩).elim
        | long moduleName id =>
          apply globalValues (.long moduleName id) val
          · simp
          · simpa [nsLookup_append_long, alistToNs, nsLookupMod] using lookup
      · exact globalConstructors
  apply canPmatchAll_rows_noTypeError genv
    { compMap with v := bindLocals traces locals compMap.v } compMap trace env st flat
    (fun _ => True) envInv rfl invariant.1 invariant.2.1
    (invariantImpStateRel interp g gen genv idxs st flat invariant) v v' values pes can
end Flapjack.Compiler.Backend.SourceToFlat
