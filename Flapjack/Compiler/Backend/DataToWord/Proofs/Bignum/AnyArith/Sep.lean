module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapWordList
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
public import Flapjack.Compiler.Backend.GcShared

@[expose] public section

/-! Separation-logic helpers for the `AnyArith_thm` port (Flapjack-only; they
play the role of HOL's `SEP_CLAUSES`, `SEP_EXISTS_THM` and `AC STAR_COMM STAR_ASSOC`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

instance anyArithStarAssoc {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩

instance anyArithStarComm {α : Type} : Std.Commutative (SetSep.star (α := α)) :=
  ⟨SetSep.starComm⟩

theorem starExists_left {α β : Type} (P : β → (α → Prop) → Prop) (Q : (α → Prop) → Prop) :
    SetSep.star (SetSep.sepExists P) Q = SetSep.sepExists (fun x => SetSep.star (P x) Q) := by
  funext h
  apply propext
  constructor
  · rintro ⟨u, v, sp, ⟨x, px⟩, q⟩; exact ⟨x, u, v, sp, px, q⟩
  · rintro ⟨x, u, v, sp, px, q⟩; exact ⟨u, v, sp, ⟨x, px⟩, q⟩

theorem starEmp_right {α : Type} (P : (α → Prop) → Prop) : SetSep.star P SetSep.emp = P := by
  rw [SetSep.starComm]; exact StackRemove.StackHeap.starEmptyLeft P

theorem starEmp_left {α : Type} (P : (α → Prop) → Prop) : SetSep.star SetSep.emp P = P :=
  StackRemove.StackHeap.starEmptyLeft P

/-- Peel an existential word list off the left of a separating conjunction. -/
theorem starWordListExists_left {width : Nat} [NeZero width] {β : Type}
    (a : BitVec width) (n : Nat) (Q : ((BitVec width × β) → Prop) → Prop)
    (h : (BitVec width × β) → Prop) (H : SetSep.star (Misc.wordListExists a n) Q h) :
    ∃ xs : List β, xs.length = n ∧ SetSep.star (Misc.wordList a xs) Q h := by
  rw [Misc.wordListExists, starExists_left] at H
  obtain ⟨xs, H⟩ := H
  refine ⟨xs, ?_⟩
  have e : SetSep.star (SetSep.star (Misc.wordList a xs) (SetSep.cond (xs.length = n))) Q =
      SetSep.star (SetSep.star (Misc.wordList a xs) Q) (SetSep.cond (xs.length = n)) := by ac_rfl
  rw [e, StackRemove.WordListExists.starCond] at H
  exact ⟨H.2, H.1⟩

theorem wordList_cons {width : Nat} [NeZero width] {β : Type} (a : BitVec width) (x : β) (xs : List β) :
    Misc.wordList a (x :: xs) =
      SetSep.star (SetSep.one (a, x)) (Misc.wordList (a + StackRemove.bytesInWord width) xs) := rfl

theorem wordList_single {width : Nat} [NeZero width] {β : Type} (a : BitVec width) (x : β) :
    Misc.wordList a [x] = SetSep.one (a, x) := by
  rw [wordList_cons]; exact starEmp_right _

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
