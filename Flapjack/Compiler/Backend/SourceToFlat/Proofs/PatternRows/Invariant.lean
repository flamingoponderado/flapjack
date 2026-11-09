module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocal
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows

@[expose] public section

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

/-- Extract the constructor-relevant global environment invariant from the full environment relation. -/
private theorem factoredEnvAllRel_globalInv (genv : GlobalEnv) (compMap : Environment)
    (env : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (related : FactoredEnvAllRel genv compMap env flatEnv locals) :
    GlobalEnvInv genv compMap (fun _ => True) env := by
  obtain ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localRel⟩ := related
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

/-- Related values match consistently under the complete compilation invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "pmatch_invariant"
  (fmap_as_finite_support := [c, tys])]
theorem pmatch_invariant {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (g : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (idxs : NextIndices × NextIndices × Set (Nat × IndexKind)) (st : State F)
    (flat : FlatSem.State C F) (compMap2 : Environment) (env : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) (compMap : Environment)
    (v : Value) (v' : FlatSem.Value) (p : Pat)
    (premises : factoredInvariant interp g gen genv idxs st flat ∧
      FactoredEnvAllRel genv compMap2 env flatEnv locals ∧ compMap2.c = compMap.c ∧ ValueRel genv v v') :
    MatchResultRel genv [] (pmatch env.c st.refs p v []) (FlatSem.pmatch flat (compilePat compMap p) v' []) := by
  obtain ⟨invariant, envRel, mapsEq, values⟩ := premises
  have envInv := factoredEnvAllRel_globalInv genv compMap2 env flatEnv locals envRel
  have simulation := patternSimulation genv compMap compMap2 env st flat [] (fun _ => True)
    envInv mapsEq invariant.1 invariant.2.1
    (invariantImpStateRel interp g gen genv idxs st flat invariant) p v v' [] []
    (by simpa [alistToNs, nsEmpty] using EnvRel.empty genv) values
  simpa using simulation

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
  obtain ⟨can, invariant, envRel, values⟩ := premises
  have envInv := factoredEnvAllRel_globalInv genv compMap env flatEnv locals envRel
  apply canPmatchAll_rows_noTypeError genv
    { compMap with v := bindLocals traces locals compMap.v } compMap trace env st flat
    (fun _ => True) envInv rfl invariant.1 invariant.2.1
    (invariantImpStateRel interp g gen genv idxs st flat invariant) v v' values pes can
end Flapjack.Compiler.Backend.SourceToFlat
