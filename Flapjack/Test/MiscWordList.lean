import Flapjack.Misc.WordList

namespace Flapjack.Test.MiscWordList
open Flapjack.SetSep Flapjack.Misc Flapjack.Compiler.Backend.StackRemove

-- Flapjack regression helpers for one/two-element lists; no corresponding
-- standalone HOL declarations are asserted by these specialized helpers.
private theorem singleton {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (value : β) (heap : (BitVec width × β) → Prop) :
    wordList address [value] heap ↔
      heap = (fun entry => entry = (address, value)) := by
  constructor
  · rintro ⟨first, second, partition, rfl, rfl⟩
    exact (show (fun entry => entry = (address, value)) = heap by
      simpa using partition.1).symm
  · rintro rfl
    refine ⟨(fun entry => entry = (address, value)),
      (fun _ => False), ?_, rfl, rfl⟩
    constructor
    · funext entry
      exact or_false _
    · intro entry h
      exact h.2

private theorem twoCells {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (firstValue secondValue : β)
    (heap : (BitVec width × β) → Prop) :
    wordList address [firstValue, secondValue] heap ↔
      heap = (fun entry => entry = (address, firstValue) ∨
        entry = (address + bytesInWord width, secondValue)) ∧
      (address, firstValue) ≠
        (address + bytesInWord width, secondValue) := by
  constructor
  · rintro ⟨first, second, partition, rfl, tail⟩
    have secondEq := (singleton _ _ _).mp tail
    subst second
    refine ⟨partition.1.symm, ?_⟩
    intro same
    exact partition.2 (address, firstValue) ⟨rfl, same⟩
  · rintro ⟨rfl, different⟩
    refine ⟨(fun entry => entry = (address, firstValue)),
      (fun entry => entry = (address + bytesInWord width, secondValue)),
      ⟨rfl, ?_⟩, rfl, (singleton _ _ _).mpr rfl⟩
    intro entry h
    exact different (h.1.symm.trans h.2)

-- Regression normalization retains the existential list and derives the pure
-- condition from STAR's empty partition; it is not an input success premise.
private theorem existsIff {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (length : Nat) (heap : (BitVec width × β) → Prop) :
    wordListExists address length heap ↔
      ∃ values : List β, wordList address values heap ∧ values.length = length := by
  constructor
  · rintro ⟨values, first, second, partition, listHeap, rfl, lengthEq⟩
    have heapEq : first = heap := by simpa using partition.1
    exact ⟨values, heapEq ▸ listHeap, lengthEq⟩
  · rintro ⟨values, listHeap, lengthEq⟩
    refine ⟨values, heap, (fun _ => False), ?_, listHeap, rfl, lengthEq⟩
    constructor
    · funext entry
      exact or_false _
    · intro entry h
      exact h.2

private theorem existsZero {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (heap : (BitVec width × β) → Prop) :
    wordListExists address 0 heap ↔ heap = (fun _ => False) := by
  rw [existsIff]
  constructor
  · rintro ⟨values, listHeap, lengthEq⟩
    have valuesEq := List.length_eq_zero_iff.mp lengthEq
    subst values
    exact listHeap
  · rintro rfl
    exact ⟨[], rfl, rfl⟩

example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) :
    wordList (β := β) address [] (fun _ => False) := rfl
example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) (value : β) :
    wordList address [value] (fun entry => entry = (address, value)) :=
  (singleton _ _ _).mpr rfl
example : wordList (255 : BitVec 8) [true, false]
    (fun entry => entry = (255, true) ∨ entry = (0, false)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
example : wordList (BitVec.ofNat 32 (2^32-4)) [(7 : Nat), 11]
    (fun entry => entry = (BitVec.ofNat 32 (2^32-4), 7) ∨ entry = (0, 11)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    have unequal : (7 : Nat) ≠ 11 := by decide
    exact unequal (congrArg Prod.snd h)
example : wordList (BitVec.ofNat 64 (2^64-8)) [((3, false) : Nat × Bool), (4, true)]
    (fun entry => entry = (BitVec.ofNat 64 (2^64-8), (3, false)) ∨ entry = (0, (4, true))) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg (fun entry => entry.2.2) h)
example : wordList (BitVec.ofNat 80 (2^80-10)) [true, false]
    (fun entry => entry = (BitVec.ofNat 80 (2^80-10), true) ∨ entry = (0, false)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
example : wordList (0 : BitVec 1) [true, false]
    (fun entry => entry = (0, true) ∨ entry = (0, false)) := by
  apply (twoCells _ _ _ _).mpr
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg Prod.snd h)
example (heap : (BitVec 1 × Bool) → Prop) : ¬ wordList 0 [true, true] heap := by
  intro h
  exact ((twoCells _ _ _ _).mp h).2 rfl
example (heap : (BitVec 7 × Nat) → Prop) : ¬ wordList 0 [3, 3] heap := by
  intro h
  exact ((twoCells _ _ _ _).mp h).2 rfl
example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) :
    wordListExists (β := β) address 0 (fun _ => False) := (existsZero _ _).mpr rfl
example {width : Nat} [NeZero width] {β : Type} (address : BitVec width) (value : β) :
    wordListExists address 1 (fun entry => entry = (address, value)) := by
  apply (existsIff _ _ _).mpr
  exact ⟨[value], (singleton _ _ _).mpr rfl, rfl⟩
example : wordListExists (255 : BitVec 8) 2
    (fun entry => entry = (255, true) ∨ entry = (0, false)) := by
  apply (existsIff _ _ _).mpr
  refine ⟨[true, false], (twoCells _ _ _ _).mpr ⟨rfl, ?_⟩, rfl⟩
  intro h
  exact Bool.noConfusion (congrArg Prod.snd h)
example : wordListExists (0 : BitVec 1) 2
    (fun entry => entry = (0, true) ∨ entry = (0, false)) := by
  apply (existsIff _ _ _).mpr
  refine ⟨[true, false], (twoCells _ _ _ _).mpr ⟨rfl, ?_⟩, rfl⟩
  intro h
  exact Bool.noConfusion (congrArg Prod.snd h)
example : ¬ wordListExists (0 : BitVec 8) 0 (fun entry => entry = (0, true)) := by
  intro h
  have impossible := congrFun ((existsZero _ _).mp h) (0, true)
  exact (iff_of_eq impossible).mp rfl
example : ¬ wordListExists (0 : BitVec 8) 1 (fun entry => entry = (1, true)) := by
  intro h
  rcases (existsIff _ _ _).mp h with ⟨values, listHeap, lengthEq⟩
  rcases List.length_eq_one_iff.mp lengthEq with ⟨value, rfl⟩
  have heapEq := (singleton _ _ _).mp listHeap
  have bad : ((1 : BitVec 8), true) = (0, value) :=
    (iff_of_eq (congrFun heapEq (1, true))).mp rfl
  have unequal : (1 : BitVec 8) ≠ 0 := by decide
  exact unequal (congrArg Prod.fst bad)

end Flapjack.Test.MiscWordList
