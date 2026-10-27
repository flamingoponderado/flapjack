import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRel

/-! Assembly infrastructure for source-to-flat pattern preservation. The
underlying value and state relations remain subject to HOL correspondence review. -/
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
          obtain ⟨flats, ctor, related, rfl, hctor⟩ :=
            (valueRel_conv_iff genv none sources flat).mp valueRel
          subst ctor
          exact pmatch_tuple_related genv compMap sourceEnv.c sourceState.refs flatState suffix bound flatEnv
            patterns sources flats related (ih sources flats bound flatEnv envRel related)
      | _ => simp [SemanticPrimitivesHOL.pmatch, MatchResultRel]
  case pref =>
    intro pattern ih source flat bound flatEnv envRel valueRel
    cases source with
    | loc flag n =>
      have hflat := (valueRel_location_iff genv flag n flat).mp valueRel
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

/-- Existential result form of pattern simulation. This is Flapjack
infrastructure over the still-unreviewed factored relations. -/
theorem pmatch_result_related {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (shadowers : VarN → Prop)
    (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv) (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c)
    (typesOk : genvCTysOk genv.c genv.tys) (stateRel : StateRel genv sourceState flatState)
    (pattern : Pat) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valueRel : ValueRel genv source flat)
    (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
    (evaluated : SemanticPrimitivesHOL.pmatch sourceEnv.c sourceState.refs pattern source (bound ++ suffix) = result) :
    ∃ flatResult, FlatSem.pmatch flatState (compilePat compMap pattern) flat flatEnv = flatResult ∧
      MatchResultRel genv suffix result flatResult := by
  refine ⟨_, rfl, ?_⟩
  rw [← evaluated]
  exact patternSimulation genv compMap compMap2 sourceEnv sourceState flatState suffix shadowers inv mapsEq ok typesOk stateRel
    pattern source flat bound flatEnv envRel valueRel

/-- Existential result form for pattern lists. This is Flapjack infrastructure
over the still-unreviewed factored relations. -/
theorem pmatchList_result_related {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (shadowers : VarN → Prop)
    (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv) (mapsEq : compMap2.c = compMap.c)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys) (stateRel : StateRel genv sourceState flatState)
    (patterns : List Pat) (sources : List SemanticPrimitivesHOL.Value) (flats : List FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valuesRel : List.Forall₂ (ValueRel genv) sources flats)
    (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
    (evaluated : SemanticPrimitivesHOL.pmatchList sourceEnv.c sourceState.refs patterns sources (bound ++ suffix) = result) :
    ∃ flatResult, FlatSem.pmatchList flatState (patterns.map (compilePat compMap)) flats flatEnv = flatResult ∧
      MatchResultRel genv suffix result flatResult := by
  refine ⟨_, rfl, ?_⟩
  rw [← evaluated]
  exact patternListSimulation genv compMap compMap2 sourceEnv sourceState flatState suffix shadowers inv mapsEq ok typesOk stateRel
    patterns sources flats bound flatEnv envRel valuesRel

/-- Original-hypothesis shape for individual pattern simulation, over the
factored relations. It remains untagged until those relations are reviewed. -/
theorem pmatch_originalShape {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (constructors : Namespace ModN ConN (Nat × Stamp))
    (store : Store SemanticPrimitivesHOL.Value) (bindings bound suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (shadowers : VarN → Prop) (pattern : Pat)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
    (evaluated : SemanticPrimitivesHOL.pmatch constructors store pattern source bindings = result)
    (stateRel : StateRel genv sourceState flatState) (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (constructorsEq : constructors = sourceEnv.c) (mapsEq : compMap2.c = compMap.c)
    (bindingsEq : bindings = bound ++ suffix) (_globalsEq : flatState.globals = genv.v)
    (storeEq : store = sourceState.refs) (valueRel : ValueRel genv source flat)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) :
    ∃ flatResult, FlatSem.pmatch flatState (compilePat compMap pattern) flat flatEnv = flatResult ∧
      MatchResultRel genv suffix result flatResult := by
  subst constructors
  subst store
  subst bindings
  exact pmatch_result_related genv compMap compMap2 sourceEnv sourceState flatState suffix bound flatEnv
    shadowers inv mapsEq ok typesOk stateRel pattern source flat envRel valueRel result evaluated

/-- Original-hypothesis shape for pattern-list simulation, over the factored
relations. It remains untagged until those relations are reviewed. -/
theorem pmatchList_originalShape {C F : Type} (genv : GlobalEnv) (compMap compMap2 : Environment)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (constructors : Namespace ModN ConN (Nat × Stamp))
    (store : Store SemanticPrimitivesHOL.Value) (bindings bound suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (shadowers : VarN → Prop) (patterns : List Pat)
    (sources : List SemanticPrimitivesHOL.Value) (flats : List FlatSem.Value)
    (result : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
    (evaluated : SemanticPrimitivesHOL.pmatchList constructors store patterns sources bindings = result)
    (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv) (ok : genvCOk genv.c)
    (typesOk : genvCTysOk genv.c genv.tys) (constructorsEq : constructors = sourceEnv.c)
    (mapsEq : compMap2.c = compMap.c) (bindingsEq : bindings = bound ++ suffix)
    (_globalsEq : flatState.globals = genv.v) (stateRel : StateRel genv sourceState flatState)
    (storeEq : store = sourceState.refs) (valuesRel : List.Forall₂ (ValueRel genv) sources flats)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) :
    ∃ flatResult, FlatSem.pmatchList flatState (patterns.map (compilePat compMap)) flats flatEnv = flatResult ∧
      MatchResultRel genv suffix result flatResult := by
  subst constructors
  subst store
  subst bindings
  exact pmatchList_result_related genv compMap compMap2 sourceEnv sourceState flatState suffix bound flatEnv
    shadowers inv mapsEq ok typesOk stateRel patterns sources flats envRel valuesRel result evaluated

end Flapjack.Compiler.Backend.SourceToFlat
