import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellformed
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Fuel-aware well-formed closure states. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- All values stored in a reference are well formed. -/
def RefWellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : ClosSem.Ref ClosSem.Value → Prop
  | .valueArray values => ValuesWellFormedFuel fuel g allowed code values
  | .byteArray _ => True
  | .thunk _ value => ValueWellFormedFuel fuel g allowed code value

/-- Source globals and references contain well-formed values and source
code is empty. This bounded invariant is not tagged as HOL's unbounded
state invariant. -/
def StateWellFormedFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (state : ClosSem.State C F) : Prop :=
  (∀ value, some value ∈ state.globals → ValueWellFormedFuel fuel g allowed code value) ∧
  (∀ key entry, state.refs.lookup key = some entry → RefWellFormedFuel fuel g allowed code entry) ∧
  state.code = HolFiniteMapExact.empty

/-- Reference well-formedness survives growth of the compiler invariants. -/
theorem refWellFormedFuel_mono {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {entry : ClosSem.Ref ClosSem.Value}
    (wf : RefWellFormedFuel fuel g allowed code entry)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key value, code.lookup key = some value → code'.lookup key = some value) :
    RefWellFormedFuel fuel g' allowed' code' entry := by
  cases entry with
  | valueArray values => exact valuesWellFormedFuel_mono wf stateGrowth allowedGrowth codeGrowth
  | byteArray bytes => trivial
  | thunk mode value => exact valueWellFormedFuel_mono wf stateGrowth allowedGrowth codeGrowth

/-- State well-formedness survives growth of the compiler invariants. -/
theorem stateWellFormedFuel_mono {C F : Type} {fuel : Nat} {g g' : State} {allowed allowed' : Set Nat}
    {code code' : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state)
    (stateGrowth : stateExtends g g') (allowedGrowth : allowed ⊆ allowed')
    (codeGrowth : ∀ key value, code.lookup key = some value → code'.lookup key = some value) :
    StateWellFormedFuel fuel g' allowed' code' state := by
  obtain ⟨globals, refs, empty⟩ := wf
  refine ⟨?_, ?_, empty⟩
  · intro value member
    exact valueWellFormedFuel_mono (globals value member) stateGrowth allowedGrowth codeGrowth
  · intro key entry found
    exact refWellFormedFuel_mono (refs key entry found) stateGrowth allowedGrowth codeGrowth

/-- Changing only the clock or FFI state preserves source-state well-formedness. -/
theorem stateWellFormedFuel_clock {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (clock : Nat) :
    StateWellFormedFuel fuel g allowed code { state with clock := clock } := wf

theorem stateWellFormedFuel_ffi {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (ffi : HolFfiState F) :
    StateWellFormedFuel fuel g allowed code { state with ffi := ffi } := wf

/-- Replacing one reference with a well-formed entry preserves the state
invariant, including when the key is fresh. -/
theorem stateWellFormedFuel_updateRef {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (key : Nat) (entry : ClosSem.Ref ClosSem.Value)
    (entryWf : RefWellFormedFuel fuel g allowed code entry) :
    StateWellFormedFuel fuel g allowed code { state with refs := state.refs.updateEq (key, entry) } := by
  obtain ⟨globals, refs, empty⟩ := wf
  refine ⟨globals, ?_, empty⟩
  intro other found lookup
  by_cases same : other = key
  · subst other
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at lookup
    subst found
    exact entryWf
  · have original : state.refs.lookup other = some found := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same, Ne.symm same] using lookup
    exact refs other found original

/-- Storing a well-formed value in a global slot preserves the invariant. -/
theorem stateWellFormedFuel_updateGlobal {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (index : Nat) (value : ClosSem.Value)
    (valueWf : ValueWellFormedFuel fuel g allowed code value) :
    StateWellFormedFuel fuel g allowed code { state with globals := state.globals.set index (some value) } := by
  obtain ⟨globals, refs, empty⟩ := wf
  refine ⟨?_, refs, empty⟩
  intro found member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact globals found old
  · cases same
    exact valueWf

/-- Allocating uninitialized global slots preserves well-formedness. -/
theorem stateWellFormedFuel_allocGlobals {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (count : Nat) :
    StateWellFormedFuel fuel g allowed code
      { state with globals := state.globals ++ List.replicate count none } := by
  obtain ⟨globals, refs, empty⟩ := wf
  refine ⟨?_, refs, empty⟩
  intro value member
  simp at member
  exact globals value member

/-- The evaluator's empty initial state satisfies the bounded invariant. -/
theorem initialState_wellFormedFuel {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (ffi : HolFfiState F) (maxApp : Nat)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (clock : Nat) :
    StateWellFormedFuel fuel g allowed code
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) := by
  simp [StateWellFormedFuel, ClosSem.initialState, HolFiniteMapExact.empty]

/-- A successful initialized global lookup returns a well-formed value. -/
theorem stateWellFormedFuel_getGlobal {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {state : ClosSem.State C F}
    (wf : StateWellFormedFuel fuel g allowed code state) (index : Nat) (value : ClosSem.Value)
    (lookup : ClosSem.getGlobal index state.globals = some (some value)) :
    ValueWellFormedFuel fuel g allowed code value := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp lookup
  apply wf.1 value
  simpa only [eq] using List.getElem_mem bound

/-- A successful fixed-index global read returns a well-formed value and
leaves the source state unchanged. -/
theorem applyGlobal_read_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (index : Nat) (result : ClosSem.Value) (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : ClosSem.applyGlobal (.global index) [] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases found : ClosSem.getGlobal index state.globals with
  | none => simp [ClosSem.applyGlobal, found] at run
  | some slot =>
    cases slot with
    | none => simp [ClosSem.applyGlobal, found] at run
    | some value =>
      simp [ClosSem.applyGlobal, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨stateWellFormedFuel_getGlobal stateWf index value found, stateWf⟩

/-- Dynamic global reads have the same invariant, with negative indices
rejected by the evaluator. -/
theorem applyGlobal_readDynamic_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (index : Nat) (dynamicIndex : Int) (result : ClosSem.Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : ClosSem.applyGlobal (.global index) [.number dynamicIndex] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  by_cases negative : dynamicIndex < 0
  · simp [ClosSem.applyGlobal, negative] at run
  · apply applyGlobal_read_wellFormedFuel state next dynamicIndex.toNat result stateWf
    simpa [ClosSem.applyGlobal, negative] using run

/-- A successful global write preserves the source-state invariant and
returns the well-formed unit value. -/
theorem applyGlobal_set_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (index : Nat) (value result : ClosSem.Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valueWf : ValueWellFormedFuel fuel g allowed code value)
    (run : ClosSem.applyGlobal (.setGlobal index) [value] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases found : ClosSem.getGlobal index state.globals with
  | none => simp [ClosSem.applyGlobal, found] at run
  | some slot =>
    cases slot with
    | some old => simp [ClosSem.applyGlobal, found] at run
    | none =>
      simp [ClosSem.applyGlobal, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.block _ .nil, stateWellFormedFuel_updateGlobal stateWf index value valueWf⟩

/-- Successful global allocation returns unit and preserves the state
invariant for every nonnegative allocation count. -/
theorem applyGlobal_alloc_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (count : Int) (result : ClosSem.Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : ClosSem.applyGlobal .allocGlobal [.number count] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  by_cases negative : count < 0
  · simp [ClosSem.applyGlobal, negative] at run
  · simp [ClosSem.applyGlobal, negative] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.block _ .nil, stateWellFormedFuel_allocGlobals stateWf count.toNat⟩

end Flapjack.Compiler.Backend.ClosCall
