import Flapjack.Compiler.Backend.ClosCall.Proofs.StateWellformed
import Aesop

/-! Well-formed results of closure numeric primitives. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Boolean results use a well-formed nullary block. -/
theorem boolValue_wellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (value : Bool) :
    ValueWellFormedFuel fuel g allowed code (boolValue value) := by
  exact .block _ .nil

/-- Integer primitives return well-formed values on success. -/
theorem doIntApp_wellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (op : ClosLang.IntOp)
    (args : List Value) (value : Value) (run : doIntApp op args = some value) :
    ValueWellFormedFuel fuel g allowed code value := by
  unfold doIntApp at run
  repeat' split at run
  all_goals simp_all
  all_goals subst value
  all_goals try exact .number _
  all_goals try exact boolValue_wellFormedFuel fuel g allowed code _

/-- Integral word primitives return well-formed values on success. -/
theorem doWordAppIntegral_wellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (op : ClosLang.WordOp)
    (args : List Value) (value : Value) (run : doWordAppIntegral op args = some value) :
    ValueWellFormedFuel fuel g allowed code value := by
  unfold doWordAppIntegral at run
  repeat' split at run
  all_goals simp_all [Bind.bind, Option.bind_eq_some_iff, Pure.pure]
  all_goals try (obtain ⟨_, _, _, _, rfl⟩ := run; exact .number _)
  all_goals try (obtain ⟨_, _, rfl⟩ := run; first | exact .number _ | exact .word64 _)
  all_goals try subst value
  all_goals try exact boolValue_wellFormedFuel fuel g allowed code _

/-- The complete word dispatcher also covers floating-point operations,
whose results are fixed-width words or Boolean values. -/
theorem doWordApp_wellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (op : ClosLang.WordOp)
    (args : List Value) (value : Value) (run : doWordApp op args = some value) :
    ValueWellFormedFuel fuel g allowed code value := by
  unfold doWordApp at run
  split at run <;> simp_all
  all_goals try subst value
  all_goals try exact .word64 _
  all_goals try exact boolValue_wellFormedFuel fuel g allowed code _
  all_goals exact doWordAppIntegral_wellFormedFuel fuel g allowed code _ _ _ run

/-- Numeric primitive dispatch leaves state unchanged and returns a
well-formed value whenever it succeeds. -/
theorem applyNumeric_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.Op)
    (args : List Value) (state next : ClosSem.State C F) (value : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (run : applyNumeric op args state = some (value, next)) :
    ValueWellFormedFuel fuel g allowed code value ∧ StateWellFormedFuel fuel g allowed code next := by
  cases op with
  | intOp operation =>
    cases found : doIntApp operation args with
    | none => simp [applyNumeric, found] at run
    | some result =>
      simp [applyNumeric, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨doIntApp_wellFormedFuel fuel g allowed code operation args result found, stateWf⟩
  | wordOp operation =>
    cases found : doWordApp operation args with
    | none => simp [applyNumeric, found] at run
    | some result =>
      simp [applyNumeric, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨doWordApp_wellFormedFuel fuel g allowed code operation args result found, stateWf⟩
  | globOp | blockOp | memOp | ffi | thunkOp | label | install => simp [applyNumeric] at run

/-- Integer primitive dispatch preserves value and state well-formedness
for successful and rejected applications. -/
theorem doApp_int_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.IntOp)
    (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.intOp op) args state) := by
  cases applied : applyNumeric (.intOp op) args state with
  | none => simp [doApp, applied, PrimitiveResultWellFormedFuel]
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simpa [doApp, applied, PrimitiveResultWellFormedFuel] using
      applyNumeric_wellFormedFuel (.intOp op) args state next value stateWf applied

/-- Word and floating-point primitive dispatch preserves the same
fuel-aware invariant for successful and rejected applications. -/
theorem doApp_word_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.WordOp)
    (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.wordOp op) args state) := by
  cases applied : applyNumeric (.wordOp op) args state with
  | none => simp [doApp, applied, PrimitiveResultWellFormedFuel]
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simpa [doApp, applied, PrimitiveResultWellFormedFuel] using
      applyNumeric_wellFormedFuel (.wordOp op) args state next value stateWf applied

end Flapjack.Compiler.Backend.ClosCall
