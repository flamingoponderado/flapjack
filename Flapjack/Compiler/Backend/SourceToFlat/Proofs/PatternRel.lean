import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
import Flapjack.SemanticPrimitivesHOL.PatternMatch

/-! Match-result infrastructure over the factored source-to-flat value relation.
Its full correspondence to HOL remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Flapjack representation of the match-result relation. The source binding
suffix is not related to the flat bindings. This is untagged until the
underlying value relation is reviewed against HOL. -/
def MatchResultRel (genv : GlobalEnv) (suffix : List (VarN × SemanticPrimitivesHOL.Value)) :
    MatchResult (List (VarN × SemanticPrimitivesHOL.Value)) →
    MatchResult (List (VarN × FlatSem.Value)) → Prop
  | .match source, .match flat =>
    ∃ bound, source = bound ++ suffix ∧ EnvRel genv (alistToNs bound) flat
  | .noMatch, .noMatch => True
  | .typeError, _ => True
  | _, _ => False

/-- Flapjack infrastructure exposing the original three possible result shapes. -/
theorem matchResultRel_cases (genv : GlobalEnv) (suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (source : MatchResult (List (VarN × SemanticPrimitivesHOL.Value)))
    (flat : MatchResult (List (VarN × FlatSem.Value)))
    (related : MatchResultRel genv suffix source flat) :
    source = .typeError ∨ (source = .noMatch ∧ flat = .noMatch) ∨
      ∃ sourceEnv flatEnv, source = .match sourceEnv ∧ flat = .match flatEnv := by
  cases source <;> cases flat <;> simp_all [MatchResultRel]

/-- A variable-pattern binding preserves related environments. This is a
Flapjack infrastructure lemma over the factored value relation. -/
theorem matchResultRel_bind (genv : GlobalEnv) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (name : VarN)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valueRel : ValueRel genv source flat) :
    MatchResultRel genv suffix (.match ((name, source) :: (bound ++ suffix)))
      (.match ((name, flat) :: flatEnv)) := by
  refine ⟨(name, source) :: bound, rfl, ?_⟩
  change EnvRel genv (nsBind name source (alistToNs bound)) ((name, flat) :: flatEnv)
  exact .bind genv name source (alistToNs bound) flatEnv flat envRel valueRel

/-- The variable case of pattern matching preserves related bindings. This is
infrastructure over the factored value and environment relations. -/
theorem pmatch_variable_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (name : VarN)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valueRel : ValueRel genv source flat) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store (.pvar name) source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap (.pvar name)) flat flatEnv) := by
  simpa only [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat] using
    matchResultRel_bind genv suffix bound flatEnv name source flat envRel valueRel

/-- The wildcard case of pattern matching preserves related bindings. This is
infrastructure over the factored environment relation. -/
theorem pmatch_wildcard_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store .pany source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap .pany) flat flatEnv) := by
  simp only [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat, MatchResultRel]
  exact ⟨bound, rfl, envRel⟩

/-- The literal case of pattern matching preserves successful and nonmatching
results, and permits the original source type error. This is infrastructure
over the factored value and environment relations. -/
theorem pmatch_literal_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (lit : Lit)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valueRel : ValueRel genv source flat) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store (.plit lit) source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap (.plit lit)) flat flatEnv) := by
  cases source with
  | litv actual =>
    have hflat := (valueRel_literal_iff genv actual flat).mp valueRel
    subst flat
    by_cases same : lit = actual
    · simp only [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat, same, if_true, MatchResultRel]
      exact ⟨bound, rfl, envRel⟩
    · by_cases sameType : litSameType lit actual = true <;>
        simp [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat, same, sameType, MatchResultRel]
  | _ => simp [SemanticPrimitivesHOL.pmatch, MatchResultRel]

/-- The reference-pattern induction step follows the related store lookup and
the original one-slot offset. The induction hypothesis is the corresponding
pattern-preservation statement for the subpattern. This is infrastructure over
the factored value, environment, and state relations. -/
theorem pmatch_reference_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (pattern : Pat) (flag : Bool) (n : Nat)
    (stateRel : StateRel genv sourceState flatState)
    (ih : ∀ source flat, ValueRel genv source flat →
      MatchResultRel genv suffix
        (SemanticPrimitivesHOL.pmatch constructors sourceState.refs pattern source (bound ++ suffix))
        (FlatSem.pmatch flatState (compilePat compMap pattern) flat flatEnv)) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors sourceState.refs (.pref pattern) (.loc flag n) (bound ++ suffix))
      (FlatSem.pmatch flatState (compilePat compMap (.pref pattern)) (.loc flag (n + 1)) flatEnv) := by
  cases lookup : storeLookup n sourceState.refs with
  | none => simp [SemanticPrimitivesHOL.pmatch, lookup, MatchResultRel]
  | some entry =>
    cases entry with
    | refv source =>
      obtain ⟨flat, hflat, hvalue⟩ := stateRel_ref_lookup genv sourceState flatState stateRel n source lookup
      simpa [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat, lookup, hflat] using ih source flat hvalue
    | w8array _ => simp [SemanticPrimitivesHOL.pmatch, lookup, MatchResultRel]
    | varray _ => simp [SemanticPrimitivesHOL.pmatch, lookup, MatchResultRel]
    | thunk _ _ => simp [SemanticPrimitivesHOL.pmatch, lookup, MatchResultRel]

/-- Empty pattern lists preserve the related bindings. This is infrastructure
over the factored environment relation. -/
theorem pmatchList_nil_related {C F : Type} (genv : GlobalEnv)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (envRel : EnvRel genv (alistToNs bound) flatEnv) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatchList constructors store [] [] (bound ++ suffix))
      (FlatSem.pmatchList state [] [] flatEnv) := by
  simp only [SemanticPrimitivesHOL.pmatchList, FlatSem.pmatchList, MatchResultRel]
  exact ⟨bound, rfl, envRel⟩

/-- The cons case of pattern-list matching composes the head and tail induction
hypotheses for arbitrary related binding environments. This is infrastructure
over the factored value and environment relations. -/
theorem pmatchList_cons_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix : List (VarN × SemanticPrimitivesHOL.Value))
    (pattern : Pat) (patterns : List Pat) (source : SemanticPrimitivesHOL.Value)
    (sources : List SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) (flats : List FlatSem.Value)
    (headIH : ∀ bound flatEnv, EnvRel genv (alistToNs bound) flatEnv →
      MatchResultRel genv suffix
        (SemanticPrimitivesHOL.pmatch constructors store pattern source (bound ++ suffix))
        (FlatSem.pmatch state (compilePat compMap pattern) flat flatEnv))
    (tailIH : ∀ bound flatEnv, EnvRel genv (alistToNs bound) flatEnv →
      MatchResultRel genv suffix
        (SemanticPrimitivesHOL.pmatchList constructors store patterns sources (bound ++ suffix))
        (FlatSem.pmatchList state (patterns.map (compilePat compMap)) flats flatEnv))
    (bound : List (VarN × SemanticPrimitivesHOL.Value)) (flatEnv : List (VarN × FlatSem.Value))
    (envRel : EnvRel genv (alistToNs bound) flatEnv) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatchList constructors store (pattern :: patterns) (source :: sources) (bound ++ suffix))
      (FlatSem.pmatchList state ((pattern :: patterns).map (compilePat compMap)) (flat :: flats) flatEnv) := by
  have headRel := headIH bound flatEnv envRel
  cases hs : SemanticPrimitivesHOL.pmatch constructors store pattern source (bound ++ suffix) with
  | typeError =>
    simp [SemanticPrimitivesHOL.pmatchList, hs, MatchResultRel]
  | noMatch =>
    cases hf : FlatSem.pmatch state (compilePat compMap pattern) flat flatEnv with
    | typeError => simp [hs, hf, MatchResultRel] at headRel
    | «match» flatBound => simp [hs, hf, MatchResultRel] at headRel
    | noMatch =>
      have tailRel := tailIH bound flatEnv envRel
      cases hst : SemanticPrimitivesHOL.pmatchList constructors store patterns sources (bound ++ suffix) <;>
        cases hft : FlatSem.pmatchList state (patterns.map (compilePat compMap)) flats flatEnv <;>
        simp_all [SemanticPrimitivesHOL.pmatchList, FlatSem.pmatchList, MatchResultRel]
  | «match» sourceBound =>
    cases hf : FlatSem.pmatch state (compilePat compMap pattern) flat flatEnv with
    | typeError => simp [hs, hf, MatchResultRel] at headRel
    | noMatch => simp [hs, hf, MatchResultRel] at headRel
    | «match» flatBound =>
      simp only [hs, hf, MatchResultRel] at headRel
      obtain ⟨bound', rfl, nextRel⟩ := headRel
      have tailRel := tailIH bound' flatBound nextRel
      simpa [SemanticPrimitivesHOL.pmatchList, FlatSem.pmatchList, hs, hf] using tailRel

/-- The as-pattern induction step extends both binding environments before
matching the subpattern. This is infrastructure over the factored relation. -/
theorem pmatch_as_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (pattern : Pat) (name : VarN)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (envRel : EnvRel genv (alistToNs bound) flatEnv) (valueRel : ValueRel genv source flat)
    (ih : ∀ bound flatEnv, EnvRel genv (alistToNs bound) flatEnv →
      MatchResultRel genv suffix
        (SemanticPrimitivesHOL.pmatch constructors store pattern source (bound ++ suffix))
        (FlatSem.pmatch state (compilePat compMap pattern) flat flatEnv)) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store (.pas pattern name) source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap (.pas pattern name)) flat flatEnv) := by
  have nextRel : EnvRel genv (alistToNs ((name, source) :: bound)) ((name, flat) :: flatEnv) := by
    change EnvRel genv (nsBind name source (alistToNs bound)) ((name, flat) :: flatEnv)
    exact .bind genv name source (alistToNs bound) flatEnv flat envRel valueRel
  simpa [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat] using
    ih ((name, source) :: bound) ((name, flat) :: flatEnv) nextRel

/-- Type annotations disappear from compiled patterns and do not change
matching. This is infrastructure over the factored match-result relation. -/
theorem pmatch_typeAnnotation_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (pattern : Pat) (typ : AstT)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
    (ih : MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store pattern source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap pattern) flat flatEnv)) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store (.ptannot pattern typ) source (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap (.ptannot pattern typ)) flat flatEnv) := by
  simpa only [SemanticPrimitivesHOL.pmatch, compilePat] using ih

/-- The tuple-constructor case uses the related value-list length and the
pattern-list induction hypothesis. This is infrastructure over the factored
value and environment relations. -/
theorem pmatch_tuple_related {C F : Type} (genv : GlobalEnv) (compMap : Environment)
    (constructors : Namespace ModN ConN (Nat × Stamp)) (store : Store SemanticPrimitivesHOL.Value)
    (state : FlatSem.State C F) (suffix bound : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value)) (patterns : List Pat)
    (sources : List SemanticPrimitivesHOL.Value) (flats : List FlatSem.Value)
    (valuesRel : List.Forall₂ (ValueRel genv) sources flats)
    (ih : MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatchList constructors store patterns sources (bound ++ suffix))
      (FlatSem.pmatchList state (patterns.map (compilePat compMap)) flats flatEnv)) :
    MatchResultRel genv suffix
      (SemanticPrimitivesHOL.pmatch constructors store (.pcon none patterns) (.conv none sources) (bound ++ suffix))
      (FlatSem.pmatch state (compilePat compMap (.pcon none patterns)) (.conv none flats) flatEnv) := by
  have len := valuesRel.length_eq
  by_cases same : patterns.length = sources.length
  · have compatible : FlatSem.PmatchStampsOk none none flats.length flats.length := .tuple _ _ rfl
    simpa [SemanticPrimitivesHOL.pmatch, FlatSem.pmatch, compilePat, same, len, compatible] using ih
  · simp [SemanticPrimitivesHOL.pmatch, same, MatchResultRel]

end Flapjack.Compiler.Backend.SourceToFlat
