module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClock
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode
public import Flapjack.Misc.ProofTactics
public import Aesop

@[expose] public section

/-! Fields preserved by every successful closure primitive application. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

namespace ApplyConstPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end ApplyConstPort

/-- Successful global primitives preserve clock, maximum arity, code, compile
oracle and compiler. -/
private theorem applyGlobal_const {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyGlobal op args state = some (value, next)) :
    next.clock = state.clock ∧ next.maxApp = state.maxApp ∧ next.code = state.code ∧
      next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  unfoldSplit applyGlobal
  all_goals aesop

/-- Successful block primitives preserve clock, maximum arity, code, compile
oracle and compiler. -/
private theorem applyBlock_const {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyBlock op args state = some (value, next)) :
    next.clock = state.clock ∧ next.maxApp = state.maxApp ∧ next.code = state.code ∧
      next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  unfoldSplit applyBlock
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful numeric primitives preserve clock, maximum arity, code, compile
oracle and compiler. -/
private theorem applyNumeric_const {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyNumeric op args state = some (value, next)) :
    next.clock = state.clock ∧ next.maxApp = state.maxApp ∧ next.code = state.code ∧
      next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  unfoldSplit applyNumeric
  all_goals aesop

/-- Successful memory primitives preserve clock, maximum arity, code, compile
oracle and compiler. -/
private theorem applyMemory_const {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : applyMemory op args state = some (value, next)) :
    next.clock = state.clock ∧ next.maxApp = state.maxApp ∧ next.code = state.code ∧
      next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  unfoldSplit applyMemory
  all_goals aesop (add simp Option.bind_eq_some_iff)

/-- A successful primitive application preserves the clock, the maximum arity,
the code map, the compile oracle and the compiler. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "do_app_const"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_const {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (res : Value) (next : State C F)
    (run : doApp op args state = .val (res, next)) :
    next.clock = state.clock ∧ next.maxApp = state.maxApp ∧ next.code = state.code ∧
      next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  cases op with
  | globOp operation =>
    cases h : applyGlobal operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (res, next) := by simpa [doApp, h] using run
      subst pair
      exact applyGlobal_const operation args state next res h
  | blockOp operation =>
    cases h : applyBlock operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (res, next) := by simpa [doApp, h] using run
      subst pair
      exact applyBlock_const operation args state next res h
  | memOp operation =>
    cases h : applyMemory operation args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (res, next) := by simpa [doApp, h] using run
      subst pair
      exact applyMemory_const operation args state next res h
  | intOp operation =>
    cases h : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (res, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_const (.intOp operation) args state next res h
  | wordOp operation =>
    cases h : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, h] at run
    | some pair =>
      have equal : pair = (res, next) := by simpa [doApp, h] using run
      subst pair
      exact applyNumeric_const (.wordOp operation) args state next res h
  | ffi | thunkOp =>
    simp only [doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | install => simp [doApp] at run

end Flapjack.Compiler.Backend.ClosSem
