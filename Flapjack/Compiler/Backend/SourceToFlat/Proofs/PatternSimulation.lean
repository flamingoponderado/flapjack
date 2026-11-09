module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRel

@[expose] public section

/-! Source-to-flat pattern preservation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Flapjack-specific pattern simulation predicate for the factored relations. -/
def PatternSimulation {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix : List (VarN × SemanticPrimitivesHOL.Value)) (pattern : Pat) : Prop :=
  ∀ source flat bound flatEnv, EnvRel genv (alistToNs bound) flatEnv → ValueRel genv source flat →
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch sourceEnv.c sourceState.refs pattern source (bound ++ suffix))
      (FlatSem.pmatch flatState (compilePat compMap pattern) flat flatEnv)

/-- Flapjack-specific pattern-list simulation predicate for the factored relations. -/
def PatternListSimulation {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix : List (VarN × SemanticPrimitivesHOL.Value)) (patterns : List Pat) : Prop :=
  ∀ sources flats bound flatEnv, EnvRel genv (alistToNs bound) flatEnv →
    List.Forall₂ (ValueRel genv) sources flats →
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatchList sourceEnv.c sourceState.refs patterns sources (bound ++ suffix))
      (FlatSem.pmatchList flatState (patterns.map (compilePat compMap)) flats flatEnv)

/-- Source-to-flat pattern simulation over the factored relations. This is not
tagged as the HOL theorem until those relations have completed source review. -/
theorem patternSimulation {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (shadowers : VarN → Prop) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (stateRel : StateRel genv sourceState flatState) (pattern : Pat) :
    PatternSimulation genv compMap sourceEnv sourceState flatState suffix pattern := by
  apply Pat.rec
    (motive_1 := PatternSimulation genv compMap sourceEnv sourceState flatState suffix)
    (motive_2 := PatternListSimulation genv compMap sourceEnv sourceState flatState suffix)
  case pany =>
    intro source flat bound flatEnv envRel valueRel
    exact pmatch_wildcard_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv source flat envRel
  case pvar =>
    intro name source flat bound flatEnv envRel valueRel
    exact pmatch_variable_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv name source flat envRel valueRel
  case plit =>
    intro lit source flat bound flatEnv envRel valueRel
    exact pmatch_literal_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv lit source flat envRel valueRel
  case pcon =>
    intro name patterns ih source flat bound flatEnv envRel valueRel
    cases name with
    | some name =>
      apply pmatch_named_related genv compMap compMap2 sourceEnv shadowers sourceState.refs flatState suffix bound flatEnv
        name patterns source flat inv mapsEq ok typesOk valueRel
      intro sources flats related
      exact ih sources flats bound flatEnv envRel related
    | none =>
      cases source with
      | conv stamp sources =>
        cases stamp with
        | some actual => simp [SemanticPrimitivesHOL.pmatch, MatchResultRel]
        | none =>
          have shape := ((valueRel_eqns_nonGlobal).2.1 sources flat genv none).mp valueRel
          simp only [reduceCtorEq, false_and, exists_false, false_or, true_and] at shape
          obtain ⟨flats, rfl, related⟩ := shape
          exact pmatch_tuple_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv
            patterns sources flats related (ih sources flats bound flatEnv envRel related)
      | _ => simp [SemanticPrimitivesHOL.pmatch, MatchResultRel]
  case pref =>
    intro pattern ih source flat bound flatEnv envRel valueRel
    cases source with
    | loc flag n =>
      have hflat := ((valueRel_eqns_nonGlobal).2.2.1 flat n genv flag).mp valueRel
      subst flat
      apply pmatch_reference_related genv compMap sourceEnv.c sourceState flatState suffix bound flatEnv pattern flag n stateRel
      intro source flat valueRel
      exact ih source flat bound flatEnv envRel valueRel
    | _ => simp [SemanticPrimitivesHOL.pmatch, MatchResultRel]
  case pas =>
    intro pattern name ih source flat bound flatEnv envRel valueRel
    apply pmatch_as_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv pattern name source flat envRel valueRel
    intro bound flatEnv envRel
    exact ih source flat bound flatEnv envRel valueRel
  case ptannot =>
    intro pattern typ ih source flat bound flatEnv envRel valueRel
    exact pmatch_typeAnnotation_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv pattern typ source flat
      (ih source flat bound flatEnv envRel valueRel)
  case nil =>
    intro sources flats bound flatEnv envRel related
    cases sources with
    | nil => cases related; exact pmatchList_nil_related genv sourceEnv.c sourceState.refs flatState suffix bound flatEnv envRel
    | cons source sources => simp [SemanticPrimitivesHOL.pmatchList, MatchResultRel]
  case cons =>
    intro pattern patterns headIH tailIH sources flats bound flatEnv envRel related
    cases sources with
    | nil => simp [SemanticPrimitivesHOL.pmatchList, MatchResultRel]
    | cons source sources =>
      cases related with
      | cons head tail =>
        apply pmatchList_cons_related genv compMap sourceEnv.c sourceState.refs flatState suffix pattern patterns source sources _ _
        · intro bound flatEnv envRel
          exact headIH source _ bound flatEnv envRel head
        · intro bound flatEnv envRel
          exact tailIH sources _ bound flatEnv envRel tail
        · exact envRel

/-- Pattern-list simulation assembled from the pattern theorem. This is
untagged while the factored relations await full HOL correspondence review. -/
theorem patternListSimulation {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (shadowers : VarN → Prop) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (stateRel : StateRel genv sourceState flatState) (patterns : List Pat) :
    PatternListSimulation genv compMap sourceEnv sourceState flatState suffix patterns := by
  induction patterns with
  | nil =>
    intro sources flats bound flatEnv envRel related
    cases sources with
    | nil => cases related; exact pmatchList_nil_related genv sourceEnv.c sourceState.refs flatState suffix bound flatEnv envRel
    | cons source sources => simp [SemanticPrimitivesHOL.pmatchList, MatchResultRel]
  | cons pattern patterns tailIH =>
    intro sources flats bound flatEnv envRel related
    cases sources with
    | nil => simp [SemanticPrimitivesHOL.pmatchList, MatchResultRel]
    | cons source sources =>
      cases related with
      | cons head tail =>
        apply pmatchList_cons_related genv compMap sourceEnv.c sourceState.refs flatState suffix pattern patterns source sources _ _
        · intro bound flatEnv envRel
          exact patternSimulation genv compMap compMap2 sourceEnv sourceState flatState suffix shadowers inv mapsEq ok typesOk stateRel
            pattern source _ bound flatEnv envRel head
        · intro bound flatEnv envRel
          exact tailIH sources _ bound flatEnv envRel tail
        · exact envRel

namespace PatternMatchPort
/-- Roundtrip for the global environment's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end PatternMatchPort

/-- Pattern and pattern-list matching are preserved by compilation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "pmatch"
  (fmap_as_finite_support := [c, tys])]
theorem pmatch_source {C F : Type} (genv : GlobalEnv) (compMap2 : Environment)
    (shadowers : VarN → Prop) (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (compMap : Environment) :
    (∀ (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
      (pattern : Pat) (source : SemanticPrimitivesHOL.Value)
      (bindings : List (VarN × SemanticPrimitivesHOL.Value))
      (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
      (bound suffix : List (VarN × SemanticPrimitivesHOL.Value)) (flatEnv : List (VarN × FlatSem.Value))
      (flatState : FlatSem.State C F) (flat : FlatSem.Value) (sourceState : SemanticPrimitivesHOL.State F),
      SemanticPrimitivesHOL.pmatch constructors store pattern source bindings = result ∧
      StateRel genv sourceState flatState ∧ GlobalEnvInv genv compMap2 shadowers sourceEnv ∧
      genvCOk genv.c ∧ genvCTysOk genv.c genv.tys ∧ constructors = sourceEnv.c ∧
      compMap2.c = compMap.c ∧ bindings = bound ++ suffix ∧ flatState.globals = genv.v ∧
      store = sourceState.refs ∧ ValueRel genv source flat ∧ EnvRel genv (alistToNs bound) flatEnv →
      ∃ flatResult, FlatSem.pmatch flatState (compilePat compMap pattern) flat flatEnv = flatResult ∧
        MatchResultRel genv suffix result flatResult) ∧
    (∀ (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
      (patterns : List Pat) (sources : List SemanticPrimitivesHOL.Value)
      (bindings : List (VarN × SemanticPrimitivesHOL.Value))
      (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
      (bound suffix : List (VarN × SemanticPrimitivesHOL.Value)) (flatEnv : List (VarN × FlatSem.Value))
      (flatState : FlatSem.State C F) (flats : List FlatSem.Value) (sourceState : SemanticPrimitivesHOL.State F),
      SemanticPrimitivesHOL.pmatchList constructors store patterns sources bindings = result ∧
      GlobalEnvInv genv compMap2 shadowers sourceEnv ∧ genvCOk genv.c ∧ genvCTysOk genv.c genv.tys ∧
      constructors = sourceEnv.c ∧ compMap2.c = compMap.c ∧ bindings = bound ++ suffix ∧
      flatState.globals = genv.v ∧ StateRel genv sourceState flatState ∧ store = sourceState.refs ∧
      List.Forall₂ (ValueRel genv) sources flats ∧ EnvRel genv (alistToNs bound) flatEnv →
      ∃ flatResult, FlatSem.pmatchList flatState (patterns.map (compilePat compMap)) flats flatEnv = flatResult ∧
        MatchResultRel genv suffix result flatResult) := by
  constructor
  · intro constructors store pattern source bindings result bound suffix flatEnv flatState flat sourceState premises
    obtain ⟨evaluated, stateRel, inv, ok, typesOk, constructorsEq, mapsEq, bindingsEq, _, storeEq, valueRel, envRel⟩ := premises
    subst constructors
    subst store
    subst bindings
    refine ⟨_, rfl, ?_⟩
    rw [← evaluated]
    exact patternSimulation genv compMap compMap2 sourceEnv sourceState flatState suffix shadowers
      inv mapsEq ok typesOk stateRel pattern source flat bound flatEnv envRel valueRel
  · intro constructors store patterns sources bindings result bound suffix flatEnv flatState flats sourceState premises
    obtain ⟨evaluated, inv, ok, typesOk, constructorsEq, mapsEq, bindingsEq, _, stateRel, storeEq, valuesRel, envRel⟩ := premises
    subst constructors
    subst store
    subst bindings
    refine ⟨_, rfl, ?_⟩
    rw [← evaluated]
    exact patternListSimulation genv compMap compMap2 sourceEnv sourceState flatState suffix shadowers
      inv mapsEq ok typesOk stateRel patterns sources flats bound flatEnv envRel valuesRel

end Flapjack.Compiler.Backend.SourceToFlat
