import Flapjack.Compiler.Backend.ClosCall.Proofs.InvariantOrdinaryOp

/-! Related thunk inspection for direct-call simulation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem ClosProps

/-- Inspection of related thunk references preserves the outcome and mode. -/
inductive DestThunkRelFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : DestThunkResult → DestThunkResult → Prop where
  | badRef : DestThunkRelFuel fuel g allowed code .badRef .badRef
  | notThunk : DestThunkRelFuel fuel g allowed code .notThunk .notThunk
  | isThunk (mode : AstHOL.ThunkMode) (left right : Value) :
      ValueRelFuel fuel g allowed code left right →
      DestThunkRelFuel fuel g allowed code (.isThunk mode left) (.isThunk mode right)

/-- Inspecting the same pointer in related stores yields related outcomes. -/
theorem destThunk_pointer_relatedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (states : StateRelFuel fuel g allowed source target) (flag : Bool) (key : Nat) :
    DestThunkRelFuel fuel g allowed target.code (destThunk [.refPtr flag key] source.refs)
      (destThunk [.refPtr flag key] target.refs) := by
  have lookup := stateRelFuel_lookupRefs states key
  cases left : source.refs.lookup key with
  | none =>
    cases right : target.refs.lookup key with
    | none => simpa [destThunk, left, right] using DestThunkRelFuel.badRef (fuel := fuel) (g := g) (allowed := allowed) (code := target.code)
    | some value => simp [ClosMti.OptionRel, left, right] at lookup
  | some value =>
    cases right : target.refs.lookup key with
    | none => simp [ClosMti.OptionRel, left, right] at lookup
    | some next =>
      have refs : refRel (ValueRelFuel fuel g allowed target.code) value next := by
        simpa [ClosMti.OptionRel, left, right] using lookup
      cases value with
      | byteArray bytes =>
        cases next <;> simp_all [refRel, destThunk]
        exact .notThunk
      | valueArray values =>
        cases next <;> simp_all [refRel, destThunk]
        exact .notThunk
      | thunk mode value =>
        cases next with
        | byteArray bytes => simp [refRel] at refs
        | valueArray values => simp [refRel] at refs
        | thunk nextMode nextValue =>
          obtain ⟨rfl, valueRel⟩ := refs
          cases flag with
          | false => simpa [destThunk, left, right] using DestThunkRelFuel.isThunk mode value nextValue valueRel
          | true => simpa [destThunk, left, right] using DestThunkRelFuel.badRef (fuel := fuel) (g := g) (allowed := allowed) (code := target.code)

/-- Related argument lists have corresponding thunk-inspection results,
including malformed inputs and non-reference values. -/
theorem destThunk_relatedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F} {left right : List Value}
    (states : StateRelFuel fuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed target.code) left right) :
    DestThunkRelFuel fuel g allowed target.code (destThunk left source.refs) (destThunk right target.refs) := by
  cases values with
  | nil => exact .notThunk
  | @cons first next rest restNext firstRel tailRel =>
    cases tailRel with
    | nil =>
      cases firstRel <;> try exact .notThunk
      case refPtr flag address => exact destThunk_pointer_relatedFuel states flag address
    | cons head tail => cases first <;> cases next <;> exact .notThunk

/-- Storing related thunk payloads succeeds or fails together and preserves
the fuel-aware state relation on success. -/
theorem storeThunk_relatedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (states : StateRelFuel fuel g allowed source target) (key : Nat) (left right : Ref Value)
    (values : refRel (ValueRelFuel fuel g allowed target.code) left right) :
    (storeThunk key right target.refs = none → storeThunk key left source.refs = none) ∧
    (∀ refs₂, storeThunk key right target.refs = some refs₂ →
      ∃ refs₁, storeThunk key left source.refs = some refs₁ ∧
        StateRelFuel fuel g allowed { source with refs := refs₁ } { target with refs := refs₂ }) := by
  have lookup := stateRelFuel_lookupRefs states key
  cases sourceLookup : source.refs.lookup key with
  | none =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [storeThunk, sourceLookup, targetLookup]
    | some next => simp [ClosMti.OptionRel, sourceLookup, targetLookup] at lookup
  | some old =>
    cases targetLookup : target.refs.lookup key with
    | none => simp [ClosMti.OptionRel, sourceLookup, targetLookup] at lookup
    | some next =>
      have refs : refRel (ValueRelFuel fuel g allowed target.code) old next := by
        simpa [ClosMti.OptionRel, sourceLookup, targetLookup] using lookup
      cases old with
      | byteArray bytes =>
        cases next <;> simp_all [refRel, storeThunk]
      | valueArray xs =>
        cases next <;> simp_all [refRel, storeThunk]
      | thunk mode value =>
        cases next with
        | byteArray bytes => simp [refRel] at refs
        | valueArray ys => simp [refRel] at refs
        | thunk nextMode nextValue =>
          obtain ⟨rfl, _⟩ := refs
          cases mode with
          | notEvaluated =>
            constructor
            · simp [storeThunk, targetLookup]
            · intro refs₂ run
              simp [storeThunk, targetLookup] at run
              subst refs₂
              exact ⟨source.refs.updateEq (key, left), by simp [storeThunk, sourceLookup],
                stateRelFuel_updateRefs states key left right values⟩
          | evaluated => simp [storeThunk, sourceLookup, targetLookup]

/-- Updating related thunk pointers with related values fails together or
produces related stores. This is local simulation infrastructure. -/
theorem updateThunk_relatedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F} {left right : List Value}
    (states : StateRelFuel fuel g allowed source target)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed target.code) left right) (flag : Bool) (key : Nat) :
    (updateThunk [.refPtr flag key] target.refs right = none →
      updateThunk [.refPtr flag key] source.refs left = none) ∧
    (∀ refs₂, updateThunk [.refPtr flag key] target.refs right = some refs₂ →
      ∃ refs₁, updateThunk [.refPtr flag key] source.refs left = some refs₁ ∧
        StateRelFuel fuel g allowed { source with refs := refs₁ } { target with refs := refs₂ }) := by
  cases flag with
  | true => simp [updateThunk]
  | false =>
    cases values with
    | nil => simp [updateThunk]
    | @cons first next rest restNext firstRel tailRel =>
      cases tailRel with
      | nil =>
        have destRel := destThunk_relatedFuel states (List.Forall₂.cons firstRel .nil)
        cases targetDest : destThunk [next] target.refs with
        | badRef =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef => simp [updateThunk, sourceDest, targetDest]
          | notThunk => simp only [sourceDest, targetDest] at destRel; cases destRel
          | isThunk mode value => simp only [sourceDest, targetDest] at destRel; cases destRel
        | notThunk =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef => simp only [sourceDest, targetDest] at destRel; cases destRel
          | isThunk mode value => simp only [sourceDest, targetDest] at destRel; cases destRel
          | notThunk =>
            have stored := storeThunk_relatedFuel states key (.thunk .evaluated first)
              (.thunk .evaluated next) (by simpa [refRel] using firstRel)
            simpa [updateThunk, sourceDest, targetDest] using stored
        | isThunk mode value =>
          cases sourceDest : destThunk [first] source.refs with
          | badRef => simp [updateThunk, sourceDest, targetDest]
          | notThunk => simp only [sourceDest, targetDest] at destRel; cases destRel
          | isThunk mode' value' => simp [updateThunk, sourceDest, targetDest]
      | cons head tail => simp [updateThunk]

/-- Memoization of related pointer and result lists fails together or yields
related states, including malformed pointer lists. -/
theorem updateThunk_lists_relatedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {source : ClosSem.State (NumSet × C) F} {target : ClosSem.State C F}
    (sourcePointers targetPointers sourceValues targetValues : List Value)
    (states : StateRelFuel fuel g allowed source target)
    (pointers : List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourcePointers targetPointers)
    (values : List.Forall₂ (ValueRelFuel fuel g allowed target.code) sourceValues targetValues) :
    (updateThunk targetPointers target.refs targetValues = none →
      updateThunk sourcePointers source.refs sourceValues = none) ∧
    (∀ targetRefs, updateThunk targetPointers target.refs targetValues = some targetRefs →
      ∃ sourceRefs, updateThunk sourcePointers source.refs sourceValues = some sourceRefs ∧
        StateRelFuel fuel g allowed { source with refs := sourceRefs } { target with refs := targetRefs }) := by
  cases pointers with
  | nil => simp [updateThunk]
  | cons head tail =>
    cases tail with
    | cons second rest => cases head <;> simp [updateThunk]
    | nil =>
      cases head with
      | refPtr flag ptr => exact updateThunk_relatedFuel states values flag ptr
      | number _ | word64 _ | block _ | byteVector _ | closure | recclosure => simp [updateThunk]

end Flapjack.Compiler.Backend.ClosCall
