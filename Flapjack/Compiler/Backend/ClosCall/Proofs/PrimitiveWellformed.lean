import Flapjack.Compiler.Backend.ClosCall.Proofs.MemoryWellformed

/-! Well-formedness of the closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- FFI calls update only a byte array and the external state; neither
introduces unverified closure values. -/
theorem doApp_ffi_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List Value) (state : ClosSem.State C F) (stateWf : StateWellFormedFuel fuel g allowed code state) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.ffi name) args state) := by
  unfold doApp
  repeat' split
  all_goals simp_all [PrimitiveResultWellFormedFuel]
  all_goals exact ⟨.block _ .nil,
    stateWellFormedFuel_ffi (stateWellFormedFuel_updateRef stateWf _ (.byteArray _) trivial) _⟩

/-- Allocating or updating a thunk stores only a well-formed argument. -/
theorem doApp_thunk_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : Flapjack.AstHOL.ThunkOp)
    (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.thunkOp op) args state) := by
  unfold doApp
  repeat' split
  all_goals simp_all [PrimitiveResultWellFormedFuel]
  all_goals try (refine ⟨.refPtr _ _, stateWellFormedFuel_updateRef stateWf _ (.thunk _ _) ?_⟩)
  all_goals try (refine ⟨.block _ .nil, stateWellFormedFuel_updateRef stateWf _ (.thunk _ _) ?_⟩)
  all_goals exact valuesWellFormedFuel_mem argsWf (by simp)

/-- Every ordinary primitive dispatcher outcome preserves the fuel-aware
value and state invariants. Install and force-thunk evaluator control flow
is handled separately from this dispatcher and remains to be proved. -/
theorem doApp_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.Op)
    (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp op args state) := by
  cases op with
  | globOp operation => exact doApp_global_result_wellFormedFuel operation args state stateWf argsWf
  | blockOp operation => exact doApp_block_result_wellFormedFuel operation args state stateWf argsWf
  | intOp operation => exact doApp_int_result_wellFormedFuel operation args state stateWf
  | wordOp operation => exact doApp_word_result_wellFormedFuel operation args state stateWf
  | memOp operation => exact doApp_memory_result_wellFormedFuel operation args state stateWf argsWf
  | ffi name => exact doApp_ffi_result_wellFormedFuel name args state stateWf
  | thunkOp operation => exact doApp_thunk_result_wellFormedFuel operation args state stateWf argsWf
  | label | install => simp [doApp, PrimitiveResultWellFormedFuel]

end Flapjack.Compiler.Backend.ClosCall
