import Flapjack.Compiler.Backend.DataSpace.Compile
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate

/-! State and variable lemmas for data-space reservation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A successful variable read returns one value per requested name. This
is untagged until its source and carrier correspondence are reviewed. -/
theorem getVars_length {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (read : DataSem.getVars names env = some values) : values.length = names.length := by
  induction names generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name names ih =>
    cases first : DataSem.getVar name env with
    | none => simp [DataSem.getVars, first] at read
    | some value =>
      cases rest : DataSem.getVars names env with
      | none => simp [DataSem.getVars, first, rest] at read
      | some tail =>
        simp [DataSem.getVars, first, rest] at read
        subst values
        simp [ih tail rest]

/-- Stack accounting commutes with changing the available space field. -/
theorem doStack_with_space {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (space : Nat) :
    doStack op values { state with space := space } = { doStack op values state with space := space } := by
  rfl

/-- Stack accounting commutes with changing the local environment. -/
theorem doStack_with_locals {C F : Type} (op : ClosLang.Op) (values : List Value)
    (state : State C F) (locals : Spt Value) :
    doStack op values { state with locals := locals } = { doStack op values state with locals := locals } := by
  rfl

end Flapjack.Compiler.Backend.DataSpace
