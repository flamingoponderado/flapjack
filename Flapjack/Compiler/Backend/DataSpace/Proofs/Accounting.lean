module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.Cuts
public import Flapjack.Compiler.Backend.Semantics.DataSem.Space

@[expose] public section

/-! Reservation accounting used when moving space checks across assignments. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- An operation allowed without a live-name annotation does not reset
reserved space. This is auxiliary infrastructure for the hoisting proof. -/
theorem noNames_noReset (op : ClosLang.Op) (valid : DataLang.opRequiresNames op = false) :
    DataLang.opSpaceReset op = false := by
  simp [DataLang.opRequiresNames] at valid
  exact valid.1

/-- Reserving an operation's requirement plus the subsequent reservation
leaves exactly the subsequent amount after a non-resetting space check. -/
theorem doSpace_reserved {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (noReset : DataLang.opSpaceReset op = false) :
    doSpace op values { state with space := opSpaceReq op values.length + remaining } =
      some { state with space := remaining } := by
  by_cases zero : opSpaceReq op values.length = 0
  · simp [doSpace, noReset, zero]
  · have enough : ¬opSpaceReq op values.length + remaining < opSpaceReq op values.length := by omega
    simp [doSpace, noReset, zero, consumeSpace, enough]

/-- A successful operand read gives the operation requirement computed from
the argument names the same arity as that computed from the values. -/
theorem read_requirement {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (op : ClosLang.Op) (read : DataSem.getVars names env = some values) :
    opSpaceReq op names.length = opSpaceReq op values.length := by
  rw [getVars_length names env values read]

/-- For non-resetting non-install operations, the hoisted reservation
feeds exactly the remaining space to the primitive dispatcher. -/
theorem doApp_reserved {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (noReset : DataLang.opSpaceReset op = false)
    (notInstall : op ≠ .install) :
    doApp op values { state with space := opSpaceReq op values.length + remaining } =
      doAppAux op values (doStack op values (doLimSafe { state with space := remaining } op values)) := by
  have spaceRun := doSpace_reserved op values state remaining noReset
  cases op with
  | install => exact False.elim (notInstall rfl)
  | intOp intop =>
    cases intop <;> simp_all [doApp, DataLang.opSpaceReset]
  | label label => simp [doApp, spaceRun]
  | ffi name => simp [doApp, spaceRun]
  | wordOp wordop => simp [doApp, spaceRun]
  | blockOp blockop => simp [doApp, spaceRun]
  | globOp globop => simp [doApp, spaceRun]
  | memOp memop => simp [doApp, spaceRun]
  | thunkOp thunkop => simp [doApp, spaceRun]

/-- The reserved-space dispatcher equation for an operation valid in an
unannotated assignment. -/
theorem doApp_reserved_unannotated {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (valid : DataLang.opRequiresNames op = false) :
    doApp op values { state with space := opSpaceReq op values.length + remaining } =
      doAppAux op values (doStack op values (doLimSafe { state with space := remaining } op values)) := by
  have notInstall : op ≠ .install := by
    intro same
    subst op
    simp [DataLang.opRequiresNames] at valid
  exact doApp_reserved op values state remaining (noNames_noReset op valid) notInstall

end Flapjack.Compiler.Backend.DataSpace
