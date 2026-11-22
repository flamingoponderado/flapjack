module

public import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Length and singleton lemmas for source-shaped variable shifting. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open ClosLang

/-- Shifting preserves the number of top-level expressions. -/
private theorem shiftList_length_eq (xs : List Exp) (m l : Nat) (i : Spt Nat) :
    (shiftList xs m l i).length = xs.length := by
  induction xs with
  | nil => simp [shiftList]
  | cons x rest ih => simp [shiftList, ih]

/-- Shifting a list keeps its length. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_LENGTH_LEMMA"]
theorem shift_LENGTH_LEMMA (xs : List Exp) (m l : Nat) (i : Spt Nat) :
    (shiftSource xs m l i).length = xs.length := by
  rw [shiftSource_eq_shiftList]
  exact shiftList_length_eq xs m l i

/-- Shifting a singleton produces a singleton list. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_SING"]
theorem shift_SING (x : Exp) (m l : Nat) (i : Spt Nat) :
    ∃ y, shiftSource [x] m l i = [y] := by
  rw [shiftSource_eq_shiftList]
  simp [shiftList]

/-- Shifting a cons is the head of the shifted singleton consed onto the
shifted tail. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "shift_CONS"]
theorem shift_CONS (x : Exp) (xs : List Exp) (m l : Nat) (i : Spt Nat) :
    shiftSource (x :: xs) m l i =
      (let c1 := shiftSource [x] m l i
       let c2 := shiftSource xs m l i
       @holHd Exp ⟨.var .none 0⟩ c1 :: c2) := by
  rw [shiftSource_eq_shiftList, shiftSource_eq_shiftList, shiftSource_eq_shiftList]
  simp [shiftList, holHd]

/-- The shifted singleton has length one and is its own head singleton. -/
@[hol "cakeml/compiler/backend/clos_annotateScript.sml" "HD_shift"]
theorem HD_shift (x : Exp) (m l : Nat) (i : Spt Nat) :
    (shiftSource [x] m l i).length = 1 ∧
      [@holHd Exp ⟨.var .none 0⟩ (shiftSource [x] m l i)] = shiftSource [x] m l i := by
  rw [shiftSource_eq_shiftList]
  simp [shiftList, holHd]

end Flapjack.Compiler.Backend.ClosAnnotate
