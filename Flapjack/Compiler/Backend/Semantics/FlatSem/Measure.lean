import Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import Lean.Elab.Tactic.Omega

/-! Termination infrastructure for an unbounded flat evaluator. This measure
ignores names, traces and literal sizes, and is therefore not HOL's
`exp_alt_size`; the extra force-thunk weight serves the same termination role. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

mutual
/-- Flat expression weight for well-founded recursion. -/
def expWeight : FlatLang.Exp → Nat
  | .raise _ body => 1 + expWeight body
  | .handle _ body rows => 1 + expWeight body + rowsWeight rows
  | .lit _ _ => 1
  | .con _ _ args => 1 + expsWeight args
  | .varLocal _ _ => 1
  | .fn _ _ body => 1 + expWeight body
  | .app _ op args => 1 + expsWeight args + if op = .src (.thunkOp .forceThunk) then 100 else 0
  | .if_ _ cond yes no => 1 + expWeight cond + expWeight yes + expWeight no
  | .mat _ body rows => 1 + expWeight body + rowsWeight rows
  | .let_ _ _ first body => 1 + expWeight first + expWeight body
  | .letrec _ funs body => 1 + funsWeight funs + expWeight body
termination_by expr => sizeOf expr

/-- Weight of an expression list, including one unit per entry. -/
def expsWeight : List FlatLang.Exp → Nat
  | [] => 0
  | expr :: rest => 1 + expWeight expr + expsWeight rest
termination_by exprs => sizeOf exprs

/-- Weight of pattern rows, including each selected body. -/
def rowsWeight : List (FlatLang.Pat × FlatLang.Exp) → Nat
  | [] => 0
  | (_, expr) :: rest => 1 + expWeight expr + rowsWeight rest
termination_by rows => sizeOf rows

/-- Weight of recursive-function bodies. -/
def funsWeight : List (VarN × VarN × FlatLang.Exp) → Nat
  | [] => 0
  | (_, _, expr) :: rest => 1 + expWeight expr + funsWeight rest
termination_by funs => sizeOf funs
end

/-- Every expression has positive weight. -/
theorem expWeight_pos (expr : FlatLang.Exp) : 0 < expWeight expr := by
  cases expr <;> simp [expWeight] <;> omega

/-- Expression-list weight is additive over append. -/
theorem expsWeight_append (left right : List FlatLang.Exp) :
    expsWeight (left ++ right) = expsWeight left + expsWeight right := by
  induction left with
  | nil => simp [expsWeight]
  | cons expr rest ih => simp [expsWeight, ih]; omega

/-- Reversing an argument list leaves the measure unchanged. -/
theorem expsWeight_reverse (expressions : List FlatLang.Exp) :
    expsWeight expressions.reverse = expsWeight expressions := by
  induction expressions with
  | nil => rfl
  | cons expr rest ih => simp [List.reverse_cons, expsWeight_append, expsWeight, ih]; omega

/-- Pattern-row selection returns a body strictly smaller than its row list. -/
theorem pmatchRows_weight {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : State C F) (value : Value) (bindings : List (VarN × Value))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp)
    (selected : pmatchRows rows state value = .match (bindings, pattern, body)) :
    expWeight body < rowsWeight rows := by
  induction rows with
  | nil => simp [pmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    cases found : pmatch state p value [] with
    | typeError => simp [pmatchRows, found] at selected
    | noMatch =>
      have bound := ih (by simpa [pmatchRows, found] using selected)
      simp [rowsWeight]
      omega
    | «match» firstBindings =>
      cases tail : pmatchRows rest state value with
      | typeError => simp [pmatchRows, found, tail] at selected
      | noMatch =>
        simp [pmatchRows, found, tail] at selected
        rcases selected with ⟨_, _, rfl⟩
        simp [rowsWeight]
        omega
      | «match» tailMatch =>
        simp [pmatchRows, found, tail] at selected
        rcases selected with ⟨_, _, rfl⟩
        simp [rowsWeight]
        omega

/-- Successful row selection returns a body smaller than the row list. -/
theorem selectRow_weight {C F : Type} (rows : List (FlatLang.Pat × FlatLang.Exp))
    (state : State C F) (value noMatch : Value) (bindings : List (VarN × Value))
    (body : FlatLang.Exp) (selected : selectRow state rows value noMatch = .ok (bindings, body)) :
    expWeight body < rowsWeight rows := by
  cases found : pmatchRows rows state value with
  | typeError => simp [selectRow, found] at selected
  | noMatch => simp [selectRow, found] at selected
  | «match» row =>
    obtain ⟨rowBindings, pattern, expr⟩ := row
    by_cases distinct : (FlatLang.patBindings pattern).Nodup
    · simp [selectRow, found, distinct] at selected
      rcases selected with ⟨rfl, rfl⟩
      exact pmatchRows_weight rows state value rowBindings pattern expr found
    · simp [selectRow, found, distinct] at selected

/-- A successful conditional chooses one of the two original branches. -/
theorem doIf_selected {α : Type} (value : Value) (yes no result : α)
    (selected : doIf value yes no = some result) : result = yes ∨ result = no := by
  unfold doIf at selected
  repeat' split at selected <;> simp_all

/-- The thunk-forcing expansion has less weight than any force application. -/
theorem appUnit_force_weight (trace : BackendCommon.Tra) (args : List FlatLang.Exp) :
    expWeight (appUnit (.varLocal .none (ofString "f"))) <
      expWeight (.app trace (.src (.thunkOp .forceThunk)) args) := by
  simp [appUnit, expWeight, expsWeight]

/-- A clamped result cannot increase the incoming clock. -/
theorem fixClock_clock_le {C F D E α : Type} (state : State C F) (result : State D E × α) :
    (fixClock state result).1.clock ≤ state.clock := by
  exact Nat.min_le_left _ _

end Flapjack.Compiler.Backend.FlatSem
