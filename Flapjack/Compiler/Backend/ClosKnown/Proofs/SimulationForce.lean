import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationPrimitive
import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk

/-! Thunk-state simulation for known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
open ClosSem ClosProps Relations Relations.StateRelation

/-- Thunk inspection preserves its error classification and relates values
when it finds a thunk. This relation is Lean-side simulation infrastructure. -/
inductive DestThunkRel (c : Config) (g : Spt ValApprox) : DestThunkResult → DestThunkResult → Prop where
  | badRef : DestThunkRel c g .badRef .badRef
  | notThunk : DestThunkRel c g .notThunk .notThunk
  | isThunk (mode : AstHOL.ThunkMode) (left right : Value) :
      ValueRel c g left right → DestThunkRel c g (.isThunk mode left) (.isThunk mode right)

/-- A pointer into related stores has corresponding thunk-inspection results. -/
theorem destThunk_pointer_related {C F : Type} {c : Config} {g : Spt ValApprox} {source : State (Spt ValApprox × C) F} {target : State C F}
    (related : StateRel c g source target) (flag : Bool) (key : Nat) :
    DestThunkRel c g (destThunk [.refPtr flag key] source.refs)
      (destThunk [.refPtr flag key] target.refs) := by
  have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 key
  cases left : source.refs.lookup key with
  | none =>
    cases right : target.refs.lookup key with
    | none => simpa [destThunk, left, right] using DestThunkRel.badRef (c := c) (g := g)
    | some value => simp [ClosMti.OptionRel, left, right] at lookup
  | some value =>
    cases right : target.refs.lookup key with
    | none => simp [ClosMti.OptionRel, left, right] at lookup
    | some next =>
      have refs : RefRel c g value next := by simpa [ClosMti.OptionRel, left, right] using lookup
      cases refs with
      | byteArray bytes =>
        simpa [destThunk, left, right] using DestThunkRel.notThunk (c := c) (g := g)
      | valueArray values nextValues rel =>
        simpa [destThunk, left, right] using DestThunkRel.notThunk (c := c) (g := g)
      | thunk mode value next rel =>
        cases flag with
        | false => simpa [destThunk, left, right] using DestThunkRel.isThunk mode value next rel
        | true => simpa [destThunk, left, right] using DestThunkRel.badRef (c := c) (g := g)

/-- Related argument lists have corresponding thunk-inspection results in
related states, including malformed argument lists and non-reference values. -/
theorem destThunk_related {C F : Type} {c : Config} {g : Spt ValApprox} {source : State (Spt ValApprox × C) F} {target : State C F} {left right : List Value}
    (states : StateRel c g source target) (values : List.Forall₂ (ValueRel c g) left right) :
    DestThunkRel c g (destThunk left source.refs) (destThunk right target.refs) := by
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
theorem storeThunk_related {C F : Type} {c : Config} {g : Spt ValApprox} {source : State (Spt ValApprox × C) F} {target : State C F}
    (states : StateRel c g source target) (key : Nat) (left right : Ref Value)
    (values : RefRel c g left right) :
    (storeThunk key right target.refs = none → storeThunk key left source.refs = none) ∧
    (∀ refs₂, storeThunk key right target.refs = some refs₂ →
      ∃ refs₁, storeThunk key left source.refs = some refs₁ ∧
        StateRel c g { source with refs := refs₁ } { target with refs := refs₂ }) := by
  have lookup := ClosMti.fmapRel_lookup states.2.2.2.2.2.2.2.2.1 key
  cases sourceLookup : source.refs.lookup key with
  | none =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [storeThunk, sourceLookup, targetLookup]
    | some next => simp [ClosMti.OptionRel, sourceLookup, targetLookup] at lookup
  | some old =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [ClosMti.OptionRel, sourceLookup, targetLookup] at lookup
    | some next =>
      have refs : RefRel c g old next := by simpa [ClosMti.OptionRel, sourceLookup, targetLookup] using lookup
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
              (by
                rcases states with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
                exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
                  ClosMti.fmapRel_update refs key left right values, compiler, oracle⟩)⟩
        | evaluated => simp [storeThunk, sourceLookup, targetLookup]

/-- Thunk updates with related values fail together or produce related
states. This helper quantifies over successful target maps in its conclusion;
the source-shaped theorem follows below. -/
theorem updateThunk_related {C F : Type} {c : Config} {g : Spt ValApprox} {source : State (Spt ValApprox × C) F} {target : State C F}
    {left right : List Value} (states : StateRel c g source target)
    (values : List.Forall₂ (ValueRel c g) left right) (flag : Bool) (key : Nat) :
    (updateThunk [.refPtr flag key] target.refs right = none →
      updateThunk [.refPtr flag key] source.refs left = none) ∧
    (∀ refs₂, updateThunk [.refPtr flag key] target.refs right = some refs₂ →
      ∃ refs₁, updateThunk [.refPtr flag key] source.refs left = some refs₁ ∧
        StateRel c g { source with refs := refs₁ } { target with refs := refs₂ }) := by
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

/-- A successful source thunk update has a corresponding target update and
preserves the optimizer's state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "rel_update_thunk"
  (fmap_as_finite_support_relation := [State.refs, State.code, sourceRefs, targetRefs])]
theorem relUpdateThunk {C F : Type} (c : Config) (g : Spt ValApprox)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (left right : List Value) (flag : Bool) (key : Nat)
    (sourceRefs : HolFiniteMapExact Nat (Ref Value))
    (related : StateRel c g source target ∧ List.Forall₂ (ValueRel c g) left right) :
    updateThunk [.refPtr flag key] source.refs left = some sourceRefs →
      ∃ (targetRefs : HolFiniteMapExact Nat (Ref Value)),
        updateThunk [.refPtr flag key] target.refs right = some targetRefs ∧
        StateRel c g { source with refs := sourceRefs } { target with refs := targetRefs } := by
  intro sourceRun
  obtain ⟨failure, success⟩ := updateThunk_related related.1 related.2 flag key
  cases targetRun : updateThunk [.refPtr flag key] target.refs right with
  | none =>
    have impossible := failure targetRun
    rw [sourceRun] at impossible
    contradiction
  | some targetRefs =>
    obtain ⟨actualRefs, actualRun, states⟩ := success targetRefs targetRun
    rw [sourceRun] at actualRun
    cases Option.some.inj actualRun
    exact ⟨targetRefs, rfl, states⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Force
