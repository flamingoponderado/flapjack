import Flapjack.Compiler.Backend.FlatPattern.Proofs.RecursiveClosures
import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Pattern result and store lookup relations for flat pattern compilation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (MatchResult StoreValue storeLookup)
open Flapjack.SemanticPrimitivesProps

/-- Related pattern results preserve failure and type-error cases and relate
successful bindings at the current name bound. This proof-side relation uses
the unreviewed FlatPattern value relation and is not yet a tagged HOL port. -/
def MatchRel (n : Nat) : MatchResult (List (VarN × Value)) → MatchResult (List (VarN × Value)) → Prop
  | .match left, .match right => aLookupRel (fun name => decNameToNum name < n) ValueRel left right
  | .noMatch, .noMatch | .typeError, .typeError => True
  | _, _ => False

/-- A related store entry can be found at the same index on the target side. -/
theorem storeValueRel_lookup {A B : Type} {R : A → B → Prop} {left : List (StoreValue A)}
    {right : List (StoreValue B)} (related : List.Forall₂ (storeValueRel R) left right)
    (index : Nat) (value : StoreValue A) (found : storeLookup index left = some value) :
    ∃ target, storeLookup index right = some target ∧ storeValueRel R value target := by
  induction related generalizing index with
  | nil => simp [storeLookup] at found
  | @cons source target left right head tail ih =>
    cases index with
    | zero =>
      simp [storeLookup] at found
      subst value
      exact ⟨target, rfl, head⟩
    | succ index =>
      simp only [storeLookup, List.getElem?_cons_succ] at found ⊢
      exact ih index found

/-- Related reference entries contain related values at the same location. -/
theorem stateRel_lookup_ref {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (states : StateRel cfg source target) (index : Nat) (value : Value)
    (found : storeLookup index source.refs = some (.refv value)) :
    ∃ value', storeLookup index target.refs = some (.refv value') ∧ ValueRel value value' := by
  obtain ⟨entry, lookup, relation⟩ := storeValueRel_lookup states.2.1 index (.refv value) found
  cases entry <;> simp [storeValueRel] at relation
  case refv value' => exact ⟨value', lookup, relation⟩

/-- A variable pattern extends related bindings by related values. -/
theorem pmatch_var_related {C F : Type} (n : Nat) (source target : FlatSem.State C F)
    (name : VarN) (value value' : Value) (bindings bindings' : List (VarN × Value))
    (values : ValueRel value value')
    (envs : aLookupRel (fun key => decNameToNum key < n) ValueRel bindings bindings') :
    MatchRel n (FlatSem.pmatch source (.pvar name) value bindings)
      (FlatSem.pmatch target (.pvar name) value' bindings') := by
  simp only [FlatSem.pmatch, MatchRel]
  exact aLookupRel_cons _ _ _ _ _ _ _ (fun _ => values) envs

/-- Wildcard patterns leave related bindings unchanged. -/
theorem pmatch_any_related {C F : Type} (n : Nat) (source target : FlatSem.State C F)
    (value value' : Value) (bindings bindings' : List (VarN × Value))
    (envs : aLookupRel (fun key => decNameToNum key < n) ValueRel bindings bindings') :
    MatchRel n (FlatSem.pmatch source .pany value bindings)
      (FlatSem.pmatch target .pany value' bindings') := by
  simpa [FlatSem.pmatch, MatchRel] using envs

/-- Literal patterns agree on related values whenever the source match does
not raise a type error. -/
theorem pmatch_lit_related {C F : Type} (n : Nat) (source target : FlatSem.State C F)
    (lit : Lit) (value value' : Value) (bindings bindings' : List (VarN × Value))
    (values : ValueRel value value')
    (envs : aLookupRel (fun key => decNameToNum key < n) ValueRel bindings bindings')
    (safe : FlatSem.pmatch source (.plit lit) value bindings ≠ .typeError) :
    MatchRel n (FlatSem.pmatch source (.plit lit) value bindings)
      (FlatSem.pmatch target (.plit lit) value' bindings') := by
  cases value with
  | litv actual =>
    have eq := (valueRel_lit actual value').1 values
    subst value'
    by_cases same : lit = actual
    · simpa [FlatSem.pmatch, same, MatchRel] using envs
    · by_cases sameType : Flapjack.SemanticPrimitivesHOL.litSameType lit actual = true
      · simp [FlatSem.pmatch, same, sameType, MatchRel]
      · simp [FlatSem.pmatch, same, sameType] at safe
  | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
    simp [FlatSem.pmatch] at safe

/-- An as-pattern reduces to its nested pattern after adding related bindings.
The recursive hypothesis is the corresponding pattern-matching case. -/
theorem pmatch_as_related {C F : Type} (n : Nat) (source target : FlatSem.State C F)
    (pattern : FlatLang.Pat) (name : VarN) (value value' : Value) (bindings bindings' : List (VarN × Value))
    (nested : MatchRel n (FlatSem.pmatch source pattern value ((name, value) :: bindings))
      (FlatSem.pmatch target pattern value' ((name, value') :: bindings'))) :
    MatchRel n (FlatSem.pmatch source (.pas pattern name) value bindings)
      (FlatSem.pmatch target (.pas pattern name) value' bindings') := by
  simpa [FlatSem.pmatch] using nested

/-- Reference-pattern matching follows related references and then applies
the nested pattern simulation to their related contents. -/
theorem pmatch_ref_related {C F : Type} (cfg : Config) (n : Nat) (source target : FlatSem.State C F)
    (pattern : FlatLang.Pat) (value value' : Value) (bindings bindings' : List (VarN × Value))
    (states : StateRel cfg source target) (values : ValueRel value value')
    (safe : FlatSem.pmatch source (.pref pattern) value bindings ≠ .typeError)
    (nested : ∀ left right, ValueRel left right →
      FlatSem.pmatch source pattern left bindings ≠ .typeError →
      MatchRel n (FlatSem.pmatch source pattern left bindings) (FlatSem.pmatch target pattern right bindings')) :
    MatchRel n (FlatSem.pmatch source (.pref pattern) value bindings)
      (FlatSem.pmatch target (.pref pattern) value' bindings') := by
  cases value with
  | loc flag index =>
    have eq := (valueRel_loc flag index value').1 values
    subst value'
    cases found : storeLookup index source.refs with
    | none => simp [FlatSem.pmatch, found] at safe
    | some entry =>
      cases entry with
      | refv contents =>
        obtain ⟨contents', found', related⟩ := stateRel_lookup_ref cfg source target states index contents found
        have innerSafe : FlatSem.pmatch source pattern contents bindings ≠ .typeError := by
          simpa [FlatSem.pmatch, found] using safe
        simpa [FlatSem.pmatch, found, found'] using nested contents contents' related innerSafe
      | w8array _ | varray _ | thunk _ _ => simp [FlatSem.pmatch, found] at safe
  | litv _ | conv _ _ | closure _ _ _ | recclosure _ _ _ | vectorv _ =>
    simp [FlatSem.pmatch] at safe

/-- Constructor patterns preserve stamp and arity checks. The nested premise
is the corresponding simulation for the list of constructor arguments. -/
theorem pmatch_con_related {C F : Type} (n : Nat) (source target : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (value value' : Value) (bindings bindings' : List (VarN × Value))
    (values : ValueRel value value')
    (safe : FlatSem.pmatch source (.pcon stamp patterns) value bindings ≠ .typeError)
    (nested : ∀ left right, List.Forall₂ ValueRel left right →
      FlatSem.pmatchList source patterns left bindings ≠ .typeError →
      MatchRel n (FlatSem.pmatchList source patterns left bindings)
        (FlatSem.pmatchList target patterns right bindings')) :
    MatchRel n (FlatSem.pmatch source (.pcon stamp patterns) value bindings)
      (FlatSem.pmatch target (.pcon stamp patterns) value' bindings') := by
  cases value with
  | conv actual fields =>
    obtain ⟨fields', rfl, fieldsRel⟩ := (valueRel_conv actual fields value').1 values
    have lengths : fields.length = fields'.length := by
      clear safe values
      induction fieldsRel with
      | nil => rfl
      | cons _ _ ih => simp only [List.length_cons, ih]
    by_cases stamps : PmatchStampsOk stamp actual patterns.length fields.length
    · have notBad : ¬ ¬ PmatchStampsOk stamp actual patterns.length fields.length := fun h => h stamps
      by_cases same : stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = fields.length
      · have innerSafe : FlatSem.pmatchList source patterns fields bindings ≠ .typeError := by
          simpa only [FlatSem.pmatch, if_neg notBad, if_pos same] using safe
        simpa only [FlatSem.pmatch, ← lengths, if_neg notBad, if_pos same] using
          nested fields fields' fieldsRel innerSafe
      · simp only [FlatSem.pmatch, ← lengths, if_neg notBad, if_neg same, MatchRel]
    · simp [FlatSem.pmatch, stamps] at safe
  | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
    simp [FlatSem.pmatch] at safe

end Flapjack.Compiler.Backend.FlatPattern
