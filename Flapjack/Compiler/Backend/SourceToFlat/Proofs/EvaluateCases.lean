import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalLookup
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
import Flapjack.EvaluateHOL.Definition

/-! Source-to-flat lookup and variable helpers, including the HOL
`env_rel_lookup` port. The untagged helpers are Flapjack-specific infrastructure
over the factored relations and the clocked flat evaluator. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

namespace EnvRelLookupReview

/-- The global environment uses the reviewed finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end EnvRelLookupReview

/-- A local lookup in related environments produces a related flat value. -/
theorem envRel_lookup (genv : GlobalEnv) (source : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv source flat)
    (name : VarN) (value : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup source (.short name) = some value) :
    ∃ flatValue, flat.lookup name = some flatValue ∧ ValueRel genv value flatValue := by
  cases related with
  | empty => simp [nsEmpty, nsLookup] at lookup
  | bind key sourceValue sourceEnv flatEnv flatValue envRel valueRel =>
    cases sourceEnv with
    | bind sourceValues sourceModules =>
      by_cases same : key = name
      · subst name
        simp [nsBind, nsLookup] at lookup
        subst value
        exact ⟨flatValue, by simp, valueRel⟩
      · have neq : (name == key) = false := by
          change decide (name = key) = false
          simp [Ne.symm same]
        simp [nsBind, nsLookup, List.lookup_cons, neq] at lookup
        obtain ⟨found, hfound, hrel⟩ := envRel_lookup genv _ flatEnv envRel name value lookup
        exact ⟨found, by simpa [List.lookup_cons, neq] using hfound, hrel⟩
termination_by flat.length

/-- An association-list lookup is preserved by related local environments. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_lookup"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_alist_lookup (genv : GlobalEnv) (source : List (VarN × SemanticPrimitivesHOL.Value))
    (name : VarN) (value : SemanticPrimitivesHOL.Value) (flat : List (VarN × FlatSem.Value))
    (lookup : source.lookup name = some value) (related : EnvRel genv (alistToNs source) flat) :
    ∃ flatValue, ValueRel genv value flatValue ∧ flat.lookup name = some flatValue := by
  have sourceLookup : nsLookup (alistToNs source : Namespace ModN VarN SemanticPrimitivesHOL.Value)
      (.short name) = some value := by simpa [alistToNs, nsLookup] using lookup
  obtain ⟨flatValue, flatLookup, valueRel⟩ := envRel_lookup genv (alistToNs source) flat related name value sourceLookup
  exact ⟨flatValue, valueRel, flatLookup⟩

/-- Global-variable simulation using both clocked evaluators without extra fuel. -/
theorem evaluate_global_unbounded {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (statesRel : StateRel genv sourceState flatState) (globalsEq : flatState.globals = genv.v)
    (trace : List VarN) (id : Ident ModN VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv.v id = some source) (related : GlobalLookupRel genv compMap id source) :
    ∃ flat, EvaluateHOL.evaluate sourceState sourceEnv [.var id] = (sourceState, .val [source]) ∧
      FlatSem.evaluate flatEnv flatState [compileExp trace compMap (.var id)] =
        (flatState, .val [flat]) ∧ ValueRel genv source flat ∧ StateRel genv sourceState flatState := by
  obtain ⟨n, flat, t, compiled, valueRel, flatDo⟩ :=
    globalLookupRel_doApp genv compMap id source flatState globalsEq related
  refine ⟨flat, ?_, ?_, valueRel, statesRel⟩
  · simp [EvaluateHOL.evaluate, lookup]
  · simp [compileExp, compiled, compileVar, FlatSem.evaluate, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, flatDo]
end Flapjack.Compiler.Backend.SourceToFlat
