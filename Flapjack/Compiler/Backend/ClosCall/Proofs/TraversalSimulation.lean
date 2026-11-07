import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateAppExpression

/-! Control-flow cases connecting direct-call traversal to evaluation. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- The variable traversal case satisfies the fuel-aware evaluation relation.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_var_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (index : Nat) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.var trace index) initial = some (out, final)) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.var trace index) out := by
  simp [callsFuel] at run
  obtain ⟨rfl, rfl⟩ := run
  exact exprSimFuel_var fuel g allowed trace index

/-- The tick traversal case composes the simulation of its actual child output.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_tick_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.tick trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel fuel body initial = some (target, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.tick trace body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuel_tick fuel g allowed trace body target (bodyIH target bodyRun)

/-- The raise traversal case composes the simulation of its actual child output.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_raise_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.raise trace body) initial = some (out, final))
    (bodyIH : ∀ target, callsFuel fuel body initial = some (target, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.raise trace body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨target, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuel_raise fuel g allowed trace body target (bodyIH target bodyRun)

/-- The handler traversal case composes its two actual child simulations.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_handle_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.handle trace body handler) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (bodyIH : ∀ target middle, callsFuel fuel body initial = some (target, middle) →
      ExprSimFuel (C := C) (F := F) fuel g allowed body target)
    (handlerIH : ∀ target middle, callsFuel fuel handler middle = some (target, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed handler target) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.handle trace body handler) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBody, middle⟩, bodyRun, ⟨targetHandler, next⟩, handlerRun, rfl, rfl⟩ := run
  exact exprSimFuel_handle fuel g allowed trace body handler targetBody targetHandler distinct
    (bodyIH targetBody middle bodyRun) (handlerIH targetHandler middle handlerRun)

/-- The let traversal case composes its binding-list and body simulations.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_let_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.let trace bindings body) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (bindingsIH : ∀ target middle, callsListFuel fuel bindings initial = some (target, middle) →
      ExprsSimFuel (C := C) (F := F) fuel g allowed bindings target)
    (bodyIH : ∀ target middle, callsFuel fuel body middle = some (target, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed body target) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.let trace bindings body) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetBindings, middle⟩, bindingsRun, ⟨targetBody, next⟩, bodyRun, rfl, rfl⟩ := run
  exact exprSimFuel_let fuel g allowed trace bindings targetBindings body targetBody distinct
    (bindingsIH targetBindings middle bindingsRun) (bodyIH targetBody middle bodyRun)

/-- The conditional traversal case composes its three actual child simulations.
This Lean-side case is not the complete HOL simulation theorem. -/
theorem callsFuel_if_sim {C F : Type} (fuel : Nat) (g : State) (allowed : Set Nat)
    (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp) (initial final : State) (out : ClosLang.Exp)
    (run : callsFuel (fuel + 1) (.ifThenElse trace condition yes no) initial = some (out, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (conditionIH : ∀ target middle, callsFuel fuel condition initial = some (target, middle) →
      ExprSimFuel (C := C) (F := F) fuel g allowed condition target)
    (yesIH : ∀ target before after, callsFuel fuel yes before = some (target, after) →
      ExprSimFuel (C := C) (F := F) fuel g allowed yes target)
    (noIH : ∀ target middle, callsFuel fuel no middle = some (target, final) →
      ExprSimFuel (C := C) (F := F) fuel g allowed no target) :
    ExprSimFuel (C := C) (F := F) fuel g allowed (.ifThenElse trace condition yes no) out := by
  simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨targetCondition, middle1⟩, conditionRun, ⟨targetYes, middle2⟩, yesRun,
    ⟨targetNo, next⟩, noRun, rfl, rfl⟩ := run
  exact exprSimFuel_if fuel g allowed trace condition yes no targetCondition targetYes targetNo distinct
    (conditionIH targetCondition middle1 conditionRun) (yesIH targetYes middle1 middle2 yesRun)
    (noIH targetNo middle2 noRun)

/-- A successful list traversal composes the simulations of its actual
expression results, while threading the direct-call compiler state in order.
This Lean-side helper is not the complete HOL simulation theorem. -/
theorem callsListFuel_sim {C F : Type} (fuel relationFuel : Nat) (g : State) (allowed : Set Nat)
    (source target : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel source initial = some (target, final))
    (distinct : (g.2.map Prod.fst).Nodup)
    (exprIH : ∀ depth expression output before after,
      callsFuel depth expression before = some (output, after) →
      ExprSimFuel (C := C) (F := F) relationFuel g allowed expression output) :
    ExprsSimFuel (C := C) (F := F) relationFuel g allowed source target := by
  apply exprsSimFuel_of_forall₂ relationFuel g allowed distinct
  induction fuel generalizing source target initial final with
  | zero =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es => simp [callsListFuel] at run
  | succ fuel ih =>
    cases source with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; exact .nil
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', middle⟩, headRun, ⟨es', next⟩, tailRun, rfl, rfl⟩ := run
      exact .cons (exprIH fuel e e' initial middle headRun) (ih es es' middle _ tailRun)

end Flapjack.Compiler.Backend.ClosCall
