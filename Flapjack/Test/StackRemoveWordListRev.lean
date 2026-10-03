import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListRev

namespace Flapjack.Test.StackRemoveWordListRev
open Flapjack.SetSep Flapjack.Compiler.Backend.StackRemove

-- Flapjack regression helpers for one/two-element lists; no corresponding
-- standalone HOL declarations are asserted by these specialized helpers.
private theorem singleton {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (value : β) (heap : (BitVec width × β) → Prop) :
    wordListRev address [value] heap ↔
      heap = (fun entry => entry = (address - bytesInWord width, value)) := by
  constructor
  · rintro ⟨first, second, partition, rfl, rfl⟩
    exact (show (fun entry => entry = (address - bytesInWord width, value)) = heap by
      simpa using partition.1).symm
  · rintro rfl
    refine ⟨(fun entry => entry = (address - bytesInWord width, value)),
      (fun _ => False), ?_, rfl, rfl⟩
    constructor
    · funext entry
      exact or_false _
    · intro entry h
      exact h.2

private theorem twoCells {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (firstValue secondValue : β)
    (heap : (BitVec width × β) → Prop) :
    wordListRev address [firstValue, secondValue] heap ↔
      heap = (fun entry => entry = (address - bytesInWord width, firstValue) ∨
        entry = (address - bytesInWord width - bytesInWord width, secondValue)) ∧
      (address - bytesInWord width, firstValue) ≠
        (address - bytesInWord width - bytesInWord width, secondValue) := by
  constructor
  · rintro ⟨first, second, partition, rfl, tail⟩
    have secondEq := (singleton _ _ _).mp tail
    subst second
    refine ⟨partition.1.symm, ?_⟩
    intro same
    exact partition.2 (address - bytesInWord width, firstValue) ⟨rfl, same⟩
  · rintro ⟨rfl, different⟩
    refine ⟨(fun entry => entry = (address - bytesInWord width, firstValue)),
      (fun entry => entry = (address - bytesInWord width - bytesInWord width, secondValue)),
      ⟨rfl, ?_⟩, rfl, (singleton _ _ _).mpr rfl⟩
    intro entry h
    exact different (h.1.symm.trans h.2)

example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) :
    wordListRev (β := β) address [] (fun _ => False) := rfl
example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) (value : β) :
    wordListRev address [value]
      (fun entry => entry = (address - bytesInWord width, value)) :=
  (singleton _ _ _).mpr rfl
example : wordListRev (0 : BitVec 8) [true] (fun entry => entry = (255, true)) :=
  (singleton _ _ _).mpr rfl
example : wordListRev (0 : BitVec 32) [(7 : Nat)]
    (fun entry => entry = (BitVec.ofNat 32 (2^32-4), 7)) := (singleton _ _ _).mpr rfl
example : wordListRev (0 : BitVec 64) [((3, false) : Nat × Bool)]
    (fun entry => entry = (BitVec.ofNat 64 (2^64-8), (3, false))) := (singleton _ _ _).mpr rfl
example : wordListRev (0 : BitVec 80) [false]
    (fun entry => entry = (BitVec.ofNat 80 (2^80-10), false)) := (singleton _ _ _).mpr rfl
example : wordListRev (0 : BitVec 64) [true, false]
    (fun entry => entry = (BitVec.ofNat 64 (2^64-8), true) ∨ entry = (BitVec.ofNat 64 (2^64-16), false)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
-- Below eight bits the byte stride is zero. Distinct pair cells are allowed
-- even at the same address; no extra functional-heap validity is assumed.
example : wordListRev (0 : BitVec 1) [true, false]
    (fun entry => entry = (0, true) ∨ entry = (0, false)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
example (heap : (BitVec 1 × Bool) → Prop) : ¬ wordListRev 0 [true, true] heap := by
  intro h
  exact (twoCells _ _ _ _).mp h |>.2 rfl
example (heap : (BitVec 7 × Nat) → Prop) : ¬ wordListRev 0 [3, 3] heap := by
  intro h
  exact (twoCells _ _ _ _).mp h |>.2 rfl
example : ¬ wordListRev (0 : BitVec 8) [true] (fun entry => entry = (0, true)) := by
  intro h
  have heapEq := (singleton _ _ _).mp h
  have bad : ((255 : BitVec 8), true) = (0, true) :=
    (iff_of_eq (congrFun heapEq ((255 : BitVec 8), true))).mpr rfl
  have unequal : (255 : BitVec 8) ≠ 0 := by decide
  exact unequal (congrArg Prod.fst bad)

end Flapjack.Test.StackRemoveWordListRev
