module

public import Flapjack.HolRef
public import Flapjack.Pancake.PanSimp
public import Flapjack.Pancake.PanStatic
public import Flapjack.Pancake.PanStructs.CompileShapeExact

@[expose] public section

/-! First-match field lookup used by the exact structure compiler. -/

namespace Flapjack

/-! Faithful executable port of `pan_structs$afindi` from
    `cakeml/pancake/pan_structsScript.sml:25-32`; it compares keys by equality
    and returns the first zero-based matching position. -/
@[hol "cakeml/pancake/pan_structsScript.sml" "afindi_def"]
def afindi [DecidableEq α] (key : α) : List (α × β) → Option Nat
  | [] => none
  | (candidate, _) :: entries =>
      if key = candidate then some 0
      else match afindi key entries with
        | none => none
        | some index => some (index + 1)
termination_by entries => sizeOf entries
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

theorem afindi_cons [DecidableEq α] (key : α) (entry : α × β) (rest : List (α × β)) :
    afindi key (entry :: rest) =
      if key = entry.1 then some 0
      else match afindi key rest with
        | none => none
        | some index => some (index + 1) := by
  obtain ⟨candidate, value⟩ := entry
  simp [afindi]

end Flapjack
