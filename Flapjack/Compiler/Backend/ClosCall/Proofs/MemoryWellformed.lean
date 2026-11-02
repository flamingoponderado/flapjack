import Flapjack.Compiler.Backend.ClosCall.Proofs.BlockWellformed

/-! Well-formedness of closure memory operations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Memory operations whose successful results contain no source values and
whose execution does not alter the store. -/
inductive ScalarMemoryOp : ClosLang.MemOp → Prop where
  | length : ScalarMemoryOp .length
  | lengthByte : ScalarMemoryOp .lengthByte
  | derefByte : ScalarMemoryOp .derefByte
  | concatByteVec : ScalarMemoryOp .concatByteVec
  | fromListByte : ScalarMemoryOp .fromListByte
  | lengthByteVec : ScalarMemoryOp .lengthByteVec
  | derefByteVec : ScalarMemoryOp .derefByteVec
  | copyByte : ScalarMemoryOp (.copyByte true)
  | stringCmp (fast : Bool) (op : Opb) : ScalarMemoryOp (.stringCmp fast op)
  | boundsCheckArray : ScalarMemoryOp .boundsCheckArray
  | boundsCheckByte (loose : Bool) : ScalarMemoryOp (.boundsCheckByte loose)
  | configGC : ScalarMemoryOp .configGC

/-- Successful scalar memory operations produce well-formed values and do
not change the state. -/
theorem applyMemory_scalar_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.MemOp) (args : List Value)
    (state next : ClosSem.State C F) (result : Value)
    (scalar : ScalarMemoryOp op) (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : applyMemory op args state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases scalar <;> unfold applyMemory at run
  all_goals repeat' split at run
  all_goals simp_all [Bind.bind, Option.bind_eq_some_iff]
  all_goals try (obtain ⟨rfl, _⟩ := run; exact .number _)
  all_goals try (obtain ⟨rfl, _⟩ := run; exact boolValue_wellFormedFuel fuel g allowed code _)
  all_goals try (obtain ⟨rfl, _⟩ := run; exact .block _ .nil)
  all_goals try (obtain ⟨_, _, rfl, rfl⟩ := run; exact ⟨.number _, stateWf⟩)
  all_goals try (obtain ⟨_, _, rfl, rfl⟩ := run; exact ⟨.byteVector _, stateWf⟩)
  all_goals try (obtain ⟨_, _, _, _, rfl, rfl⟩ := run; exact ⟨.byteVector _, stateWf⟩)
  case h_19 =>
    obtain ⟨entry, _, run⟩ := run
    cases entry with
    | valueArray values => simp at run
    | thunk mode value => simp at run
    | byteArray bytes =>
      simp [Option.bind_eq_some_iff] at run
      obtain ⟨_, _, rfl, rfl⟩ := run
      exact ⟨.byteVector _, stateWf⟩

/-- Byte-vector-to-list conversion builds a well-formed list of numbers. -/
theorem applyMemory_toListByte_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value)
    (state next : ClosSem.State C F) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : applyMemory .toListByte args state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases args with
  | nil => simp [applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [applyMemory] at run
    | nil =>
      cases first with
      | byteVector bytes =>
        simp [applyMemory] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨listToValue_wellFormedFuel ?_, stateWf⟩
        apply valuesWellFormedFuel_of_forall
        intro value member
        obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
        exact .number _
      | number | word64 | block | refPtr | closure | recclosure => simp [applyMemory] at run

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

/-- Every accepted `el` argument form preserves well-formedness. -/
theorem applyMemory_el_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value)
    (state next : ClosSem.State C F) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : applyMemory .el args state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases args with
  | nil => simp [applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyMemory] at run
      | nil =>
        cases second with
        | number index =>
          cases first with
          | block tag fields =>
            have blockWf := valuesWellFormedFuel_mem argsWf (value := .block tag fields) (by simp)
            cases blockWf with
            | block _ fieldsWf => exact applyMemory_elBlock_wellFormedFuel state next tag fields index result stateWf fieldsWf run
          | refPtr flag key => exact applyMemory_elArray_wellFormedFuel state next flag key index result stateWf run
          | number | word64 | byteVector | closure | recclosure => simp [applyMemory] at run
        | word64 | block | byteVector | refPtr | closure | recclosure =>
          cases first <;> simp [applyMemory] at run

/-- Every successful array allocation preserves the invariant. -/
theorem applyMemory_refArray_all_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value)
    (state next : ClosSem.State C F) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : applyMemory .refArray args state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases args with
  | nil => simp [applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [applyMemory] at run
    | cons value rest =>
      cases rest with
      | cons extra rest => simp [applyMemory] at run
      | nil =>
        cases first with
        | number count =>
          exact applyMemory_refArray_wellFormedFuel state next count value result stateWf
            (valuesWellFormedFuel_mem argsWf (by simp)) run
        | word64 | block | byteVector | refPtr | closure | recclosure => simp [applyMemory] at run

/-- Every successful value-array update preserves the invariant. -/
theorem applyMemory_update_all_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value)
    (state next : ClosSem.State C F) (result : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : applyMemory .update args state = some (result, next)) :
    ValueWellFormedFuel fuel g allowed code result ∧ StateWellFormedFuel fuel g allowed code next := by
  cases args with
  | nil => simp [applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [applyMemory] at run
      | cons value rest =>
        cases rest with
        | cons extra rest => simp [applyMemory] at run
        | nil =>
          cases first with
          | refPtr flag key =>
            cases second with
            | number index =>
              exact applyMemory_update_wellFormedFuel state next flag key index value result stateWf
                (valuesWellFormedFuel_mem argsWf (by simp)) run
            | word64 | block | byteVector | refPtr | closure | recclosure => simp [applyMemory] at run
          | number | word64 | block | byteVector | closure | recclosure => simp [applyMemory] at run

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

/-- Lift a successful memory-operation preservation proof through the
primitive dispatcher, which converts unsuccessful operations to aborts. -/
theorem doApp_memory_result_of_apply {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.MemOp)
    (args : List Value) (state : ClosSem.State C F)
    (success : ∀ value next, applyMemory op args state = some (value, next) →
      ValueWellFormedFuel fuel g allowed code value ∧ StateWellFormedFuel fuel g allowed code next) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp op) args state) := by
  cases applied : applyMemory op args state with
  | none => simp [doApp, applied, PrimitiveResultWellFormedFuel]
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simpa [doApp, applied, PrimitiveResultWellFormedFuel] using success value next applied

/-- Scalar memory operations preserve the dispatcher result invariant,
including rejected input shapes and failed bounds checks. -/
theorem doApp_scalarMemory_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.MemOp)
    (args : List Value) (state : ClosSem.State C F)
    (scalar : ScalarMemoryOp op) (stateWf : StateWellFormedFuel fuel g allowed code state) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp op) args state) := by
  apply doApp_memory_result_of_apply op args state
  intro value next run
  exact applyMemory_scalar_wellFormedFuel op args state next value scalar stateWf run

/-- Byte-vector-to-list dispatch preserves the primitive result invariant. -/
theorem doApp_toListByte_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp .toListByte) args state) := by
  apply doApp_memory_result_of_apply .toListByte args state
  intro value next run
  exact applyMemory_toListByte_wellFormedFuel args state next value stateWf run

/-- Indexed block and array reads preserve the primitive result invariant. -/
theorem doApp_el_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp .el) args state) := by
  apply doApp_memory_result_of_apply .el args state
  intro value next run
  exact applyMemory_el_wellFormedFuel args state next value stateWf argsWf run

/-- Array allocation preserves the primitive result invariant. -/
theorem doApp_refArray_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp .refArray) args state) := by
  apply doApp_memory_result_of_apply .refArray args state
  intro value next run
  exact applyMemory_refArray_all_wellFormedFuel args state next value stateWf argsWf run

/-- Value-array updates preserve the primitive result invariant. -/
theorem doApp_update_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.memOp .update) args state) := by
  apply doApp_memory_result_of_apply .update args state
  intro value next run
  exact applyMemory_update_all_wellFormedFuel args state next value stateWf argsWf run

end Flapjack.Compiler.Backend.ClosCall
