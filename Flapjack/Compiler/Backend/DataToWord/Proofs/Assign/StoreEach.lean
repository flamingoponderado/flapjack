module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreList
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Evaluation of the generated word-list stores. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace StoreEachAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end StoreEachAssignmentWitness

/-- Memory-only updates preserve register reads, as used in the HOL induction. -/
private theorem getVarsMemory {width : Nat} [NeZero width] {C F : Type}
    (xs : List Nat) (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width) :
    WordSemStateFiniteExact.getVars xs {s with memory := m} = WordSemStateFiniteExact.getVars xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, ih]

/-- The arbitrary-offset induction used in the HOL proof. -/
private theorem storeEachGeneral {width : Nat} [NeZero width] {C F : Type}
    (base : Nat) (xs : List Nat) (ys : List (WordLocW width))
    (s : WordSemStateFiniteExact width C F) (addr offset : BitVec width)
    (memory : BitVec width → WordLocW width)
    (stored : storeList (addr + offset) ys s.memory s.mdomain = some memory)
    (args : WordSemStateFiniteExact.getVars xs s = some ys)
    (baseRead : WordSemStateFiniteExact.getVar base s = some (.word addr)) :
    WordSemStateFiniteExact.evaluate (storeEach base xs offset) s =
      (none, {s with memory := memory}) := by
  induction xs generalizing ys s offset memory with
  | nil =>
    simp [WordSemStateFiniteExact.getVars] at args
    subst ys
    simp [storeList] at stored
    subst memory
    simp [storeEach, WordSemStateFiniteExact.evaluate]
  | cons x xs ih =>
    cases head : WordSemStateFiniteExact.getVar x s with
    | none => simp [WordSemStateFiniteExact.getVars, head] at args
    | some val =>
      cases rest : WordSemStateFiniteExact.getVars xs s with
      | none => simp [WordSemStateFiniteExact.getVars, head, rest] at args
      | some vals =>
        have eq : ys = val :: vals := by simpa [WordSemStateFiniteExact.getVars, head, rest] using args.symm
        subst ys
        by_cases inside : s.mdomain (addr + offset) = true
        · let mem := fun k => if k = addr + offset then val else s.memory k
          let t := {s with memory := mem}
          have tail : storeList (addr + (offset + wordSemBytesInWord)) vals t.memory t.mdomain = some memory := by
            simpa [storeList, inside, mem, t, BitVec.add_assoc] using stored
          have tailArgs : WordSemStateFiniteExact.getVars xs t = some vals := by
            simpa [t, getVarsMemory] using rest
          have tailBase : WordSemStateFiniteExact.getVar base t = some (.word addr) := by
            simpa [t, WordSemStateFiniteExact.getVar] using baseRead
          have recursive := ih vals t (offset + wordSemBytesInWord) memory tail tailArgs tailBase
          simp [storeEach, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.memStore, WordSemStateFiniteExact.fixClock,
            baseRead, head, inside, mem, t, theWords, wordOpHOL, wordOp, recursive]
        · simp [storeList, inside] at stored

/-- Executing the generated stores writes the same list as `storeList`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_StoreEach"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_storeEach {width : Nat} [NeZero width] {C F : Type}
    (ys : List (WordLocW width)) (xs : List Nat) (t : WordSemStateFiniteExact width C F)
    (i : Nat) (a : BitVec width) (memory : BitVec width → WordLocW width) :
    storeList a ys t.memory t.mdomain = some memory ∧
      WordSemStateFiniteExact.getVars xs t = some ys ∧
      WordSemStateFiniteExact.getVar i t = some (.word a) →
    WordSemStateFiniteExact.evaluate (storeEach i xs 0) t = (none, {t with memory := memory}) := by
  rintro ⟨stored, args, base⟩
  exact storeEachGeneral i xs ys t a 0 memory (by simpa using stored) args base

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
