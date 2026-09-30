import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec

namespace Flapjack.WordAlloc

/-- Decode the shared exact-carrier colouring recursion for execution.
Flapjack infrastructure: the generic production word type has no HOL original. -/
def applyColourExpExecutable {α : Type u} (f : Nat → Nat) (e : WordExp α) : WordExp α :=
  wordExpFromHOL (applyColourExpCore f (wordExpToHOL e))

@[simp] theorem applyColourExpExecutable_const {α : Type u} (f : Nat → Nat) (v : α) :
    applyColourExpExecutable f (.const v) = .const v := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore]

@[simp] theorem applyColourExpExecutable_var {α : Type u} (f : Nat → Nat) (n : Nat) :
    applyColourExpExecutable (α := α) f (.var n) = .var (f n) := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore]

@[simp] theorem applyColourExpExecutable_lookup {α : Type u} (f : Nat → Nat)
    (s : WordStore α) : applyColourExpExecutable f (.lookup s) = .lookup s := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore]

@[simp] theorem applyColourExpExecutable_load {α : Type u} (f : Nat → Nat) (e : WordExp α) :
    applyColourExpExecutable f (.load e) = .load (applyColourExpExecutable f e) := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore]

@[simp] theorem applyColourExpExecutable_op {α : Type u} (f : Nat → Nat)
    (op : BinOp) (es : List (WordExp α)) :
    applyColourExpExecutable f (.op op es) = .op op (es.map (applyColourExpExecutable f)) := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore, List.map_map]

@[simp] theorem applyColourExpExecutable_shift {α : Type u} (f : Nat → Nat)
    (sh : Shift) (left right : WordExp α) :
    applyColourExpExecutable f (.shift sh left right) =
      .shift sh (applyColourExpExecutable f left) (applyColourExpExecutable f right) := by
  simp [applyColourExpExecutable, wordExpToHOL, wordExpFromHOL, applyColourExpCore]

/-- The executed codec route commutes with the reviewed HOL-shaped definition.
This relates Flapjack's two carriers, so it has no standalone HOL original. -/
theorem applyColourExpExecutable_commutes {width : Nat} [NeZero width]
    (f : Nat → Nat) (e : WordExp (BitVec width)) :
    wordExpToHOL (applyColourExpExecutable f e) = applyColourExp f (wordExpToHOL e) := by
  exact wordExpToHOL_fromHOL _

end Flapjack.WordAlloc
