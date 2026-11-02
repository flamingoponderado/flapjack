import Flapjack.Compiler.Backend.ClosCall.Proofs.BlockWellformed

/-! Well-formedness of closure memory operations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- A list filled with a well-formed value is well formed. -/
theorem valuesWellFormedFuel_replicate {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (count : Nat) (value : Value)
    (wf : ValueWellFormedFuel fuel g allowed code value) :
    ValuesWellFormedFuel fuel g allowed code (List.replicate count value) := by
  induction count with
  | zero => exact .nil
  | succ count ih => exact .cons wf ih

/-- Replacing a list element with a well-formed value preserves the list
invariant, including out-of-range updates. -/
theorem valuesWellFormedFuel_set {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (values : List Value) (index : Nat) (value : Value)
    (valuesWf : ValuesWellFormedFuel fuel g allowed code values)
    (valueWf : ValueWellFormedFuel fuel g allowed code value) :
    ValuesWellFormedFuel fuel g allowed code (values.set index value) := by
  apply valuesWellFormedFuel_of_forall
  intro found member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valuesWellFormedFuel_mem valuesWf old
  · subst found; exact valueWf

/-- An array retrieved from a well-formed state has well-formed contents. -/
theorem stateWellFormedFuel_lookupArray {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state : ClosSem.State C F)
    (key : Nat) (values : List Value) (stateWf : StateWellFormedFuel fuel g allowed code state)
    (found : state.refs.lookup key = some (.valueArray values)) :
    ValuesWellFormedFuel fuel g allowed code values := stateWf.2.1 key _ found

/-- Allocating a reference from a well-formed value list preserves the
state invariant and produces a well-formed pointer. -/
theorem applyMemory_ref_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (values : List Value) (result : Value) (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valuesWf : ValuesWellFormedFuel fuel g allowed code values)
    (run : applyMemory .ref values state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  simp [applyMemory] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.refPtr _ _, stateWellFormedFuel_updateRef stateWf _ (.valueArray values) valuesWf⟩

/-- Array allocation preserves the invariant for any successful size. -/
theorem applyMemory_refArray_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (count : Int) (value result : Value) (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valueWf : ValueWellFormedFuel fuel g allowed code value)
    (run : applyMemory .refArray [.number count, value] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  by_cases negative : count < 0
  · simp [applyMemory, negative] at run
  · simp [applyMemory, negative] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.refPtr _ _, stateWellFormedFuel_updateRef stateWf _ (.valueArray _)
      (valuesWellFormedFuel_replicate count.toNat value valueWf)⟩

/-- A successful value-array update preserves both the returned unit value
and the reference-store invariant. -/
theorem applyMemory_update_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (flag : Bool) (key : Nat) (index : Int) (value result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valueWf : ValueWellFormedFuel fuel g allowed code value)
    (run : applyMemory .update [.refPtr flag key, .number index, value] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases found : state.refs.lookup key with
  | none => simp [applyMemory, found] at run
  | some entry =>
    cases entry with
    | byteArray bytes => simp [applyMemory, found] at run
    | thunk mode old => simp [applyMemory, found] at run
    | valueArray values =>
      have arrayWf := stateWellFormedFuel_lookupArray state key values stateWf found
      by_cases bad : index < 0 ∨ index.toNat ≥ values.length
      · simp [applyMemory, found, bad] at run
      · simp [applyMemory, found, bad] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.block _ .nil, stateWellFormedFuel_updateRef stateWf key (.valueArray _)
          (valuesWellFormedFuel_set values index.toNat value arrayWf valueWf)⟩

/-- A successful indexed read from a value array returns a well-formed
element and leaves the source state unchanged. -/
theorem applyMemory_elArray_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (flag : Bool) (key : Nat) (index : Int) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : applyMemory .el [.refPtr flag key, .number index] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases found : state.refs.lookup key with
  | none => simp [applyMemory, found] at run
  | some entry =>
    cases entry with
    | byteArray bytes => simp [applyMemory, found] at run
    | thunk mode old => simp [applyMemory, found] at run
    | valueArray values =>
      have arrayWf := stateWellFormedFuel_lookupArray state key values stateWf found
      by_cases negative : index < 0
      · simp [applyMemory, found, negative] at run
      · cases selected : values[index.toNat]? with
        | none => simp [applyMemory, found, negative, selected] at run
        | some value =>
          simp [applyMemory, found, negative, selected] at run
          obtain ⟨rfl, rfl⟩ := run
          obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp selected
          have member : value ∈ values := by simpa only [eq] using List.getElem_mem bound
          exact ⟨valuesWellFormedFuel_mem arrayWf member, stateWf⟩

/-- A successful indexed read from a block returns one of its well-formed
fields and leaves the state unchanged. -/
theorem applyMemory_elBlock_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (state next : ClosSem.State C F)
    (tag : Nat) (values : List Value) (index : Int) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (valuesWf : ValuesWellFormedFuel fuel g allowed code values)
    (run : applyMemory .el [.block tag values, .number index] state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  by_cases negative : index < 0
  · simp [applyMemory, negative] at run
  · cases selected : values[index.toNat]? with
    | none => simp [applyMemory, negative, selected] at run
    | some value =>
      simp [applyMemory, negative, selected] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp selected
      have member : value ∈ values := by simpa only [eq] using List.getElem_mem bound
      exact ⟨valuesWellFormedFuel_mem valuesWf member, stateWf⟩

/-- Reference allocation preserves the primitive result invariant for all
well-formed arguments. -/
theorem doApp_ref_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp .ref) args state) := by
  cases applied : applyMemory .ref args state with
  | none => simp [doApp, applied, PrimitiveResultWellFormedFuel]
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simpa [doApp, applied, PrimitiveResultWellFormedFuel] using
      applyMemory_ref_wellFormedFuel state next args value stateWf argsWf applied

end Flapjack.Compiler.Backend.ClosCall
