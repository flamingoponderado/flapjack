module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
public import Flapjack.Compiler.Backend.LabToTarget.InstMem
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateStack

@[expose] public section

/-! Concrete writes to a separated packed byte payload. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- Exchange the first two separated assertions while retaining the frame. -/
theorem star_swap_first {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- Writing one element of a separated word list updates exactly its graph
entry and preserves the entire external separation frame. -/
theorem wordList_write {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (values : List β) (i : Nat) (newValue : β)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (frame : ((BitVec width × β) → Prop) → Prop) (bound : i < values.length)
    (separated : SetSep.star (Misc.wordList address values) frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star (Misc.wordList address (values.set i newValue)) frame
      (SetSep.fun2Set ((fun key => if key = address + BitVec.ofNat width i * StackRemove.bytesInWord width
        then newValue else memory key), domain)) := by
  classical
  induction values generalizing address i frame with
  | nil => simp at bound
  | cons value values ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      have changed := SetSep.writeFun2Set newValue address value _ memory domain separated
      rw [SetSep.starComm] at changed
      convert changed using 2
      congr 1
      funext key
      by_cases h : key = address <;> simp [h]
    | succ i =>
      simp only [List.set_cons_succ, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      rw [star_swap_first] at separated
      have changed := ih (address + StackRemove.bytesInWord width) i
        (SetSep.star (SetSep.one (address, value)) frame) (by simpa using bound) separated
      rw [star_swap_first] at changed
      have addressEq : (address + StackRemove.bytesInWord width) +
          BitVec.ofNat width i * StackRemove.bytesInWord width =
          address + BitVec.ofNat width (i + 1) * StackRemove.bytesInWord width := by
        simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        ac_rfl
      simpa only [addressEq] using changed

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
