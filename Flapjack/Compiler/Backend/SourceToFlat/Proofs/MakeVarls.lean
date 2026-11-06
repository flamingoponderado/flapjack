import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalWeakening
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateClock
import Flapjack.Misc.ListEl

/-! Evaluation of the generated global initialization expression. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

private instance : Nonempty VarN := ⟨Flapjack.Basis.Pure.MlString.ofString ""⟩
private instance : Nonempty FlatSem.Value := ⟨.conv none []⟩

/-- A single local binding initializes a previously empty global slot. -/
theorem evaluate_globalVarInit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (name : VarN) (value : FlatSem.Value) (idx : Nat)
    (lookup : env.v.lookup name = some value) (empty : state.globals[idx]? = some none) :
    FlatSem.evaluate env state [.app .none (.globalVarInit idx) [.varLocal .none name]] =
      ({ state with globals := state.globals.set idx (some value) }, .val [FlatSem.unitValue]) := by
  simp [FlatSem.evaluate, lookup, FlatSem.fixClock, FlatSem.applyResult,
    FlatSem.doApp, FlatSem.doAppFlat, empty]

/-- Initializing the first blank after a prefix replaces exactly that slot. -/
theorem evaluate_globalVarInit_after_prefix {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (name : VarN) (value : FlatSem.Value) (pre post : List (Option FlatSem.Value))
    (lookup : env.v.lookup name = some value) (slots : state.globals = pre ++ none :: post) :
    FlatSem.evaluate env state [.app .none (.globalVarInit pre.length) [.varLocal .none name]] =
      ({ state with globals := pre ++ some value :: post }, .val [FlatSem.unitValue]) := by
  have empty : state.globals[pre.length]? = some none := by
    rw [slots]
    simp
  rw [evaluate_globalVarInit env state name value pre.length lookup empty]
  simp [slots, List.set_append_right]

/-- The generated initializer writes each looked-up value into its reserved
slot, preserving the prefix and suffix. The lookup relation is the pointwise
form of the indexed premise used in the original proof. -/
theorem evaluate_makeVarls {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List VarN) (values : List FlatSem.Value)
    (lookups : List.Forall₂ (fun name value => env.v.lookup name = some value) names values)
    (pre post : List (Option FlatSem.Value)) (state : FlatSem.State C F)
    (n : Nat) (trace : Tra)
    (slots : state.globals = pre ++ (List.replicate names.length none ++ post)) :
    FlatSem.evaluate env state [makeVarls n trace pre.length names] =
      ({ state with globals := pre ++ (values.map some ++ post) }, .val [FlatSem.unitValue]) := by
  induction lookups generalizing pre state n trace with
  | nil =>
    cases state
    simp_all [makeVarls, FlatSem.evaluate, FlatSem.unitValue]
  | @cons name value names values lookup rest ih =>
    have firstSlots : state.globals = pre ++ none :: (List.replicate names.length none ++ post) := by
      simpa [List.replicate_succ, List.append_assoc] using slots
    have first := evaluate_globalVarInit_after_prefix env state name value pre
      (List.replicate names.length none ++ post) lookup firstSlots
    cases names with
    | nil =>
      cases rest
      simpa [makeVarls, List.replicate_succ, List.append_assoc] using first
    | cons next more =>
      rw [makeVarls, FlatSem.evaluate]
      rw [first]
      simp only [FlatSem.fixClock]
      -- Remaining initializations use the just-written prefix.
      have nextSlots : ({ state with globals := pre ++ some value ::
          (List.replicate (next :: more).length none ++ post) } : FlatSem.State C F).globals =
          (pre ++ [some value]) ++ (List.replicate (next :: more).length none ++ post) := by
        simp [List.append_assoc]
      have next := ih (pre ++ [some value]) _ (n + 1) .none nextSlots
      simpa [List.append_assoc] using next
      all_goals simp

/-- The indexed lookup condition from the original initializer theorem gives
the pointwise relation needed by the evaluation proof. -/
theorem lookup_forall₂_of_indices (env : FlatSem.Environment FlatSem.Value)
    (names : List VarN) (values : List FlatSem.Value)
    (length : values.length = names.length)
    (lookups : ∀ (i : Nat) (inValues : i < values.length),
      env.v.lookup (names[i]'(by omega)) = some values[i]) :
    List.Forall₂ (fun name value => env.v.lookup name = some value) names values := by
  induction names generalizing values with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons _ _ => simp at length
  | cons name names ih =>
    cases values with
    | nil => simp at length
    | cons value values =>
      have tailLength : values.length = names.length := by simpa using length
      apply List.Forall₂.cons
      · have h := lookups 0 (by simp)
        change env.v.lookup name = some value at h
        exact h
      · apply ih values tailLength
        intro i inValues
        have h := lookups (i + 1) (by simpa using inValues)
        change env.v.lookup (names[i]'(by omega)) = some values[i] at h
        exact h

/-- Initialization of the reserved globals from the local environment. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "evaluate_make_varls"]
theorem evaluate_makeVarls_indexed {C F : Type} (n : Nat) (trace : Tra) (idx : Nat)
    (names : List VarN) (pre post : List (Option FlatSem.Value)) (state : FlatSem.State C F)
    (env : FlatSem.Environment FlatSem.Value) (values : List FlatSem.Value) (len : Nat)
    (premises : state.globals = pre ++ List.replicate len none ++ post ∧
      pre.length = idx ∧ values.length = names.length ∧ len = names.length ∧
      (∀ i, i < values.length → env.v.lookup (Flapjack.holEl i names) = some (Flapjack.holEl i values))) :
    FlatSem.evaluate env state [makeVarls n trace idx names] =
      ({ state with globals := pre ++ values.map some ++ post }, .val [.conv none []]) := by
  obtain ⟨slots, prefixLength, length, slotLength, lookups⟩ := premises
  subst idx
  subst len
  have indexed : ∀ (i : Nat) (inValues : i < values.length),
      env.v.lookup (names[i]'(by omega)) = some values[i] := by
    intro i inValues
    simpa only [Flapjack.holEl_eq_getElem i names (by omega),
      Flapjack.holEl_eq_getElem i values inValues] using lookups i inValues
  have result := evaluate_makeVarls env names values (lookup_forall₂_of_indices env names values length indexed)
    pre post state n trace (by simpa [List.append_assoc] using slots)
  simpa [List.append_assoc, FlatSem.unitValue] using result

/-- Executing the initializer also grows the global relation: previously
initialized slots retain their values when the reserved block is filled. -/
theorem evaluate_makeVarls_growth {C F : Type} (genv : GlobalEnv)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (n : Nat) (trace : Tra) (idx len : Nat) (names : List VarN) (values : List FlatSem.Value)
    (pre post : List (Option FlatSem.Value))
    (globals : state.globals = genv.v)
    (slots : state.globals = pre ++ (List.replicate len none ++ post))
    (prefixLength : pre.length = idx) (length : values.length = names.length)
    (slotLength : len = names.length)
    (lookups : ∀ (i : Nat) (inValues : i < values.length),
      env.v.lookup (names[i]'(by omega)) = some values[i]) :
    FlatSem.evaluate env state [makeVarls n trace idx names] =
        ({ state with globals := pre ++ (values.map some ++ post) }, .val [FlatSem.unitValue]) ∧
      GlobalGrowth genv { genv with v := pre ++ (values.map some ++ post) } := by
  have totalLookups : ∀ i, i < values.length →
      env.v.lookup (Flapjack.holEl i names) = some (Flapjack.holEl i values) := by
    intro i inValues
    simpa only [Flapjack.holEl_eq_getElem i names (by omega),
      Flapjack.holEl_eq_getElem i values inValues] using lookups i inValues
  refine ⟨?_, ?_⟩
  · simpa [List.append_assoc, FlatSem.unitValue] using
      evaluate_makeVarls_indexed n trace idx names pre post state env values len
        ⟨by simpa [List.append_assoc] using slots, prefixLength, length, slotLength, totalLookups⟩
  · apply GlobalGrowth.fillNone genv pre (values.map some) post
    simpa [List.length_map, length, slotLength] using globals.symm.trans slots

/-- Updating the flat global slots and weakening the global relation preserves
the factored state relation; references, clock, and FFI are unchanged. -/
theorem stateRel_after_global_growth {C F : Type} (old new : GlobalEnv)
    (growth : GlobalGrowth old new) (source : SemanticPrimitivesHOL.State F)
    (state : FlatSem.State C F) (related : StateRel old source state)
    (newSlots : List (Option FlatSem.Value)) :
    StateRel new source { state with globals := newSlots } := by
  have weakened := stateRel_growth old new growth source state related
  cases weakened with
  | intro nonempty refs clock ffi =>
    exact .intro source _ nonempty refs clock ffi

end Flapjack.Compiler.Backend.SourceToFlat
