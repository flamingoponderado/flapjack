module

public import Flapjack.FiniteMap.BroadCodec

public import Flapjack.Misc.Option.Rel
public import Flapjack.Compiler.Backend.ClosMti.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk
public import Flapjack.Compiler.Backend.BackendProps.Pure

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! State relation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosSem BackendProps

private def maptoBroadlookup {K V : Type} (map : HolFiniteMapExact K V) : K → Option V := map.lookup
private def mapofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical lookup and support roundtrip for the first map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_first {K A : Type} (first : HolFiniteMapExact K A) :
    mapofBroad (maptoBroadlookup first) first.finiteSupport = first := by cases first; rfl

/-- Canonical lookup and support roundtrip for the second map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_second {K B : Type} (second : HolFiniteMapExact K B) :
    mapofBroad (maptoBroadlookup second) second.finiteSupport = second := by cases second; rfl

/-- Equal finite-map domains with related values at every source key. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "FMAP_REL_def"
  (fmap_as_finite_support_parameters := [first, second])]
def fmapRel {K A B : Type} (r : A → B → Prop) (first : HolFiniteMapExact K A)
    (second : HolFiniteMapExact K B) : Prop :=
  (∀ k, first.lookup k ≠ none ↔ second.lookup k ≠ none) ∧
    ∀ k v, first.lookup k = some v → ∃ w, second.lookup k = some w ∧ r v w

/-- The closure-state finite-map representation and its lookup view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Relate closure states across multi-argument introduction. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
noncomputable def StateRel {C F : Type} (source target : State C F) : Prop :=
  (∀ n, (source.compileOracle n).2.2 = [] ∧
    ∀ e ∈ (source.compileOracle n).2.1, ClosProps.noMti e) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧
  target.clock = source.clock ∧ target.ffi = source.ffi ∧
  List.Forall₂ (ValueRelOpt source.maxApp) source.globals target.globals ∧
  fmapRel (RefRel source.maxApp) source.refs target.refs ∧
  source.compile = pureCc (compileInc source.maxApp) target.compile ∧
  target.compileOracle = pureCo (compileInc source.maxApp) ∘ source.compileOracle

/-- Related states agree on clock and application limit. -/
theorem stateRel_clock_maxApp {C F : Type} {source target : State C F}
    (related : StateRel source target) :
    source.clock = target.clock ∧ source.maxApp = target.maxApp ∧ 1 ≤ target.maxApp := by
  obtain ⟨_, _, _, maxEq, maxPos, clockEq, _⟩ := related
  exact ⟨clockEq.symm, maxEq.symm, maxEq ▸ maxPos⟩

/-- A related pair of finite maps has related lookup results at every key. -/
theorem fmapRel_lookup {K A B : Type} {r : A → B → Prop}
    {first : HolFiniteMapExact K A} {second : HolFiniteMapExact K B}
    (related : fmapRel r first second) (key : K) :
    optionRel r (first.lookup key) (second.lookup key) := by
  obtain ⟨domain, values⟩ := related
  cases left : first.lookup key with
  | none =>
    cases right : second.lookup key with
    | none => trivial
    | some value =>
      have same := domain key
      simp [left, right] at same
  | some value =>
    obtain ⟨next, found, rel⟩ := values key value left
    rw [found]
    exact rel

/-- Updating corresponding keys with related values preserves the finite-map
relation, including the domains and all untouched lookups. -/
theorem fmapRel_update {K A B : Type} [DecidableEq K] {r : A → B → Prop}
    {first : HolFiniteMapExact K A} {second : HolFiniteMapExact K B}
    (related : fmapRel r first second) (key : K) (left : A) (right : B) (values : r left right) :
    fmapRel r (first.updateEq (key, left)) (second.updateEq (key, right)) := by
  obtain ⟨domain, entries⟩ := related
  constructor
  · intro k
    by_cases equal : k = key
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal]
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using domain k
  · intro k value found
    by_cases equal : k = key
    · subst k
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst value
      exact ⟨right, by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL], values⟩
    · have original : first.lookup k = some value := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using found
      obtain ⟨next, lookup, rel⟩ := entries k value original
      exact ⟨next, by simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using lookup, rel⟩

/-- Related states expose related references at every address. -/
theorem stateRel_lookupRefs {C F : Type} {source target : State C F}
    (related : StateRel source target) (key : Nat) :
    optionRel (RefRel source.maxApp) (source.refs.lookup key) (target.refs.lookup key) := by
  exact fmapRel_lookup related.2.2.2.2.2.2.2.2.1 key

/-- Either reference lookup can be completed with the related lookup from the
other state. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "state_rel_opt_rel_refs"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelOptRelRefs {C F : Type} (source target : State C F) (key : Nat)
    (left right : Option (Ref Value)) :
    (StateRel source target ∧ source.refs.lookup key = left →
      ∃ right', target.refs.lookup key = right' ∧ optionRel (RefRel source.maxApp) left right') ∧
    (StateRel source target ∧ target.refs.lookup key = right →
      ∃ left', source.refs.lookup key = left' ∧ optionRel (RefRel source.maxApp) left' right) := by
  constructor
  · rintro ⟨states, lookup⟩
    exact ⟨target.refs.lookup key, rfl, lookup ▸ stateRel_lookupRefs states key⟩
  · rintro ⟨states, lookup⟩
    exact ⟨source.refs.lookup key, rfl, lookup ▸ stateRel_lookupRefs states key⟩

/-- Updating both reference stores with related entries preserves the state
relation. This is a Lean-side step toward the source thunk-update theorem. -/
theorem stateRel_updateRefs {C F : Type} {source target : State C F}
    (related : StateRel source target) (key : Nat) (left right : Ref Value)
    (values : RefRel source.maxApp left right) :
    StateRel { source with refs := source.refs.updateEq (key, left) }
      { target with refs := target.refs.updateEq (key, right) } := by
  obtain ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, ffi, globals, refs, compiler, nextOracle⟩ := related
  exact ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, ffi, globals,
    fmapRel_update refs key left right values, compiler, nextOracle⟩

/-- Replacing both FFI states preserves the relation. -/
theorem stateRel_withFfi {C F : Type} {source target : State C F}
    (related : StateRel source target) (ffi : HolFfiState F) :
    StateRel { source with ffi := ffi } { target with ffi := ffi } := by
  obtain ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, _, globals, refs, compiler, nextOracle⟩ := related
  exact ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, rfl, globals, refs, compiler, nextOracle⟩

/-- Replacing both global lists with related lists preserves the relation. -/
theorem stateRel_withGlobals {C F : Type} {source target : State C F}
    (related : StateRel source target) (left right : List (Option Value))
    (globals : List.Forall₂ (ValueRelOpt source.maxApp) left right) :
    StateRel { source with globals := left } { target with globals := right } := by
  obtain ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, ffi, _, refs, compiler, nextOracle⟩ := related
  exact ⟨oracle, sourceCode, targetCode, maxApp, positive, clock, ffi, globals, refs, compiler, nextOracle⟩

/-- Advancing both compiler oracles and replacing both clocks preserves the
multi-argument state relation. This is Lean-side simulation infrastructure. -/
theorem stateRel_shiftClock {C F : Type} {source target : State C F}
    (related : StateRel source target) (clock amount : Nat) :
    StateRel { source with clock := clock, compileOracle := Flapjack.holShiftSeq amount source.compileOracle }
      { target with clock := clock, compileOracle := Flapjack.holShiftSeq amount target.compileOracle } := by
  obtain ⟨oracle, sourceCode, targetCode, maxApp, positive, _, ffi, globals, refs, compiler, nextOracle⟩ := related
  refine ⟨?_, sourceCode, targetCode, maxApp, positive, rfl, ffi, globals, refs, compiler, ?_⟩
  · intro n
    exact oracle (n + amount)
  · funext n
    change target.compileOracle (n + amount) =
      pureCo (compileInc source.maxApp) (source.compileOracle (n + amount))
    rw [nextOracle]
    rfl

/-- The multi-argument state relation meets the generic simple-state
conditions used by primitive-operation simulations. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "simple_state_rel"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel {C F : Type} (maxApp : Nat) :
    ClosProps.simpleStateRel (ValueRel maxApp)
      (fun (s t : State C F) => s.maxApp = maxApp ∧ StateRel s t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, eq, states⟩
    have lookup := stateRel_lookupRefs states ptr
    cases left : s.refs.lookup ptr <;> simp_all [optionRel]
  · intro bytes t s ptr ⟨found, eq, states⟩
    have lookup := stateRel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [optionRel, left] at lookup
    | some value =>
      have refs : RefRel s.maxApp value (.byteArray bytes) := by simpa [optionRel, left] using lookup
      cases refs
      rfl
  · intro values t s ptr ⟨found, eq, states⟩
    have lookup := stateRel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [optionRel, left] at lookup
    | some value =>
      have refs : RefRel s.maxApp value (.valueArray values) := by simpa [optionRel, left] using lookup
      cases refs with
      | valueArray leftValues _ rel =>
        exact ⟨leftValues, rfl, by simpa [eq] using rel⟩
  · intro mode value t s ptr ⟨found, eq, states⟩
    have lookup := stateRel_lookupRefs states ptr
    rw [found] at lookup
    cases left : s.refs.lookup ptr with
    | none => simp [optionRel, left] at lookup
    | some old =>
      have refs : RefRel s.maxApp old (.thunk mode value) := by simpa [optionRel, left] using lookup
      cases refs with
      | thunk _ leftValue _ rel =>
        exact ⟨leftValue, rfl, by simpa [eq] using rel⟩
  · intro s t ⟨eq, states⟩
    obtain ⟨_, _, _, _, _, _, ffi, globals, refs, _, _⟩ := states
    refine ⟨ffi.symm, refs.1, ?_⟩
    have same : ValueRelOpt maxApp = Flapjack.optionRel (ValueRel maxApp) := by
      funext a b; cases a <;> cases b <;> rfl
    simpa [eq, same] using globals
  · intro ffi s t ⟨eq, states⟩
    exact ⟨eq, stateRel_withFfi states ffi⟩
  · intro bytes s t ptr ⟨eq, states⟩
    exact ⟨eq, stateRel_updateRefs states ptr _ _ (.byteArray bytes)⟩
  · intro s t ptr xs ys ⟨⟨eq, states⟩, values⟩
    apply And.intro eq
    apply stateRel_updateRefs states ptr _ _
    exact .valueArray xs ys (by simpa [eq] using values)
  · intro s t ptr mode v w ⟨⟨eq, states⟩, values⟩
    apply And.intro eq
    apply stateRel_updateRefs states ptr _ _
    exact .thunk mode v w (by simpa [eq] using values)
  · intro s t xs ys ⟨⟨eq, states⟩, values⟩
    apply And.intro eq
    apply stateRel_withGlobals states xs ys
    have same : ValueRelOpt maxApp = Flapjack.optionRel (ValueRel maxApp) := by
      funext a b; cases a <;> cases b <;> rfl
    simpa [eq, same] using values

/-- Thunk inspection preserves its error classification and relates values
when it finds a thunk. This relation is Lean-side simulation infrastructure. -/
inductive DestThunkRel (maxApp : Nat) : DestThunkResult → DestThunkResult → Prop where
  | badRef : DestThunkRel maxApp .badRef .badRef
  | notThunk : DestThunkRel maxApp .notThunk .notThunk
  | isThunk (mode : AstHOL.ThunkMode) (left right : Value) :
      ValueRel maxApp left right → DestThunkRel maxApp (.isThunk mode left) (.isThunk mode right)

/-- A pointer into related stores has corresponding thunk-inspection results. -/
theorem destThunk_pointer_related {C F : Type} {source target : State C F}
    (related : StateRel source target) (flag : Bool) (key : Nat) :
    DestThunkRel source.maxApp (destThunk [.refPtr flag key] source.refs)
      (destThunk [.refPtr flag key] target.refs) := by
  have lookup := stateRel_lookupRefs related key
  cases left : source.refs.lookup key with
  | none =>
    cases right : target.refs.lookup key with
    | none => simpa [destThunk, left, right] using DestThunkRel.badRef (maxApp := source.maxApp)
    | some value => simp [optionRel, left, right] at lookup
  | some value =>
    cases right : target.refs.lookup key with
    | none => simp [optionRel, left, right] at lookup
    | some next =>
      have refs : RefRel source.maxApp value next := by simpa [optionRel, left, right] using lookup
      cases refs with
      | byteArray bytes =>
        simpa [destThunk, left, right] using DestThunkRel.notThunk (maxApp := source.maxApp)
      | valueArray values nextValues rel =>
        simpa [destThunk, left, right] using DestThunkRel.notThunk (maxApp := source.maxApp)
      | thunk mode value next rel =>
        cases flag with
        | false => simpa [destThunk, left, right] using DestThunkRel.isThunk mode value next rel
        | true => simpa [destThunk, left, right] using DestThunkRel.badRef (maxApp := source.maxApp)

/-- Related argument lists have corresponding thunk-inspection results in
related states, including malformed argument lists and non-reference values. -/
theorem destThunk_related {C F : Type} {source target : State C F} {left right : List Value}
    (states : StateRel source target) (values : List.Forall₂ (ValueRel source.maxApp) left right) :
    DestThunkRel source.maxApp (destThunk left source.refs) (destThunk right target.refs) := by
  cases values with
  | nil => exact .notThunk
  | @cons first next rest restNext firstRel tailRel =>
    cases tailRel with
    | nil =>
      cases firstRel <;> try exact .notThunk
      case refPtr flag address => exact destThunk_pointer_related states flag address
    | cons head tail => cases first <;> cases next <;> exact .notThunk

/-- Storing related thunk payloads succeeds or fails together and preserves
the state relation on success. This is Lean-side simulation infrastructure. -/
theorem storeThunk_related {C F : Type} {source target : State C F}
    (states : StateRel source target) (key : Nat) (left right : Ref Value)
    (values : RefRel source.maxApp left right) :
    (storeThunk key right target.refs = none → storeThunk key left source.refs = none) ∧
    (∀ refs₂, storeThunk key right target.refs = some refs₂ →
      ∃ refs₁, storeThunk key left source.refs = some refs₁ ∧
        StateRel { source with refs := refs₁ } { target with refs := refs₂ }) := by
  have lookup := stateRel_lookupRefs states key
  cases sourceLookup : source.refs.lookup key with
  | none =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [storeThunk, sourceLookup, targetLookup]
    | some next => simp [optionRel, sourceLookup, targetLookup] at lookup
  | some old =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [optionRel, sourceLookup, targetLookup] at lookup
    | some next =>
      have refs : RefRel source.maxApp old next := by simpa [optionRel, sourceLookup, targetLookup] using lookup
      cases refs with
      | byteArray bytes => simp [storeThunk, sourceLookup, targetLookup]
      | valueArray xs ys rel => simp [storeThunk, sourceLookup, targetLookup]
      | thunk mode old next rel =>
        cases mode with
        | notEvaluated =>
          constructor
          · simp [storeThunk, targetLookup]
          · intro refs₂ run
            simp [storeThunk, targetLookup] at run
            subst refs₂
            exact ⟨source.refs.updateEq (key, left), by simp [storeThunk, sourceLookup],
              stateRel_updateRefs states key left right values⟩
        | evaluated => simp [storeThunk, sourceLookup, targetLookup]

/-- Thunk updates with related values fail together or produce related
states. This helper quantifies over successful target maps in its conclusion;
the source-shaped theorem follows below. -/
theorem updateThunk_related {C F : Type} {source target : State C F}
    {left right : List Value} (states : StateRel source target)
    (values : List.Forall₂ (ValueRel source.maxApp) left right) (flag : Bool) (key : Nat) :
    (updateThunk [.refPtr flag key] target.refs right = none →
      updateThunk [.refPtr flag key] source.refs left = none) ∧
    (∀ refs₂, updateThunk [.refPtr flag key] target.refs right = some refs₂ →
      ∃ refs₁, updateThunk [.refPtr flag key] source.refs left = some refs₁ ∧
        StateRel { source with refs := refs₁ } { target with refs := refs₂ }) := by
  cases flag with
  | true => simp [updateThunk]
  | false =>
    cases values with
    | nil => simp [updateThunk]
    | @cons first next rest restNext firstRel tailRel =>
      cases tailRel with
      | nil =>
        have destRel := destThunk_related states (List.Forall₂.cons firstRel .nil)
        cases targetDest : destThunk [next] target.refs with
        | badRef =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef => simp [updateThunk, sourceDest, targetDest]
          | notThunk =>
            simp only [sourceDest, targetDest] at destRel
            cases destRel
          | isThunk mode value =>
            simp only [sourceDest, targetDest] at destRel
            cases destRel
        | notThunk =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef =>
            simp only [sourceDest, targetDest] at destRel
            cases destRel
          | isThunk mode value =>
            simp only [sourceDest, targetDest] at destRel
            cases destRel
          | notThunk =>
            have stored := storeThunk_related states key (.thunk .evaluated first)
              (.thunk .evaluated next) (.thunk .evaluated first next firstRel)
            simpa [updateThunk, sourceDest, targetDest] using stored
        | isThunk mode value =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef => simp [updateThunk, sourceDest, targetDest]
          | notThunk =>
            simp only [sourceDest, targetDest] at destRel
            cases destRel
          | isThunk mode' value' => simp [updateThunk, sourceDest, targetDest]
      | cons head tail => simp [updateThunk]

/-- The closure state roundtrips through its canonical finite-map view. -/
theorem holFmapAsFiniteSupportRelationWitness_State {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Canonical codec for the existential reference-map witness. -/
theorem holFmapAsFiniteSupportExistentialWitness_relUpdateThunk_sourceRefs
    (sourceRefs : HolFiniteMapExact Nat (Ref Value)) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs)).lookup = sourceRefs.lookup ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs)).finiteSupport = sourceRefs.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad sourceRefs) = sourceRefs := by
  cases sourceRefs
  exact ⟨rfl, rfl, rfl⟩

/-- Source-shaped thunk-update simulation, with the target reference map
quantified outside both implications. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "rel_update_thunk"
  (fmap_as_finite_support_relation := [State.refs, State.code, targetRefs])
  (fmap_as_finite_support_existentials := [sourceRefs])]
theorem relUpdateThunk {C F : Type} (source target : State C F)
    (left right : List Value) (flag : Bool) (key : Nat)
    (targetRefs : HolFiniteMapExact Nat (Ref Value))
    (related : StateRel source target ∧ List.Forall₂ (ValueRel source.maxApp) left right) :
    (updateThunk [.refPtr flag key] target.refs right = none →
      updateThunk [.refPtr flag key] source.refs left = none) ∧
    (updateThunk [.refPtr flag key] target.refs right = some targetRefs →
      ∃ (sourceRefs : HolFiniteMapExact Nat (Ref Value)),
        updateThunk [.refPtr flag key] source.refs left = some sourceRefs ∧
        StateRel { source with refs := sourceRefs } { target with refs := targetRefs }) := by
  obtain ⟨failure, success⟩ := updateThunk_related related.1 related.2 flag key
  exact ⟨failure, success targetRefs⟩

end Flapjack.Compiler.Backend.ClosMti
