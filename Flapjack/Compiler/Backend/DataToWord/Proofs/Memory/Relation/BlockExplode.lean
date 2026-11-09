module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

@[expose] public section

/-! Relating block fields to a consecutive sequence of concrete words. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Every address corresponding to a list element lies in the memory domain.
The unused memory and list-element carriers remain independently polymorphic. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "eq_assum_def"
  (words_as_type_indexed_bitvec)]
def eqAssum {width : Nat} [NeZero width] {β γ : Type} (address : BitVec width)
    (memory : β) (domain : BitVec width → Bool) : List γ → Prop
  | [] => True
  | _ :: rest => domain address = true ∧ eqAssum (address + StackRemove.bytesInWord width) memory domain rest

/-- Pair every source value with the concrete word at its consecutive address.
The unused domain and the list and memory carriers are independent. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "eq_explode_def"
  (words_as_type_indexed_bitvec)]
def eqExplode {width : Nat} [NeZero width] {α β δ : Type} (address : BitVec width)
    (memory : BitVec width → β) (domain : δ) : List α → List (α × β)
  | [] => []
  | value :: rest => (value, memory address) ::
      eqExplode (address + StackRemove.bytesInWord width) memory domain rest

/-- The exploded sequence distributes over a list append. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "eq_explode_APPEND"
  (words_as_type_indexed_bitvec)]
theorem eqExplode_append {width : Nat} [NeZero width] {α β δ : Type}
    (xs ys : List α) (address : BitVec width) (memory : BitVec width → β) (domain : δ) :
    eqExplode address memory domain (xs ++ ys) = eqExplode address memory domain xs ++
      eqExplode (address + BitVec.ofNat width xs.length * StackRemove.bytesInWord width) memory domain ys := by
  induction xs generalizing address with
  | nil => simp [eqExplode]
  | cons head tail ih =>
    simp only [List.cons_append, eqExplode, ih, List.length_cons]
    congr 2
    simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
    congr 1
    ac_rfl

/-- The domain condition distributes over a list append. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "eq_assum_APPEND"
  (words_as_type_indexed_bitvec)]
theorem eqAssum_append {width : Nat} [NeZero width] {β γ : Type}
    (xs ys : List γ) (address : BitVec width) (memory : β) (domain : BitVec width → Bool) :
    eqAssum address memory domain (xs ++ ys) ↔ eqAssum address memory domain xs ∧
      eqAssum (address + BitVec.ofNat width xs.length * StackRemove.bytesInWord width) memory domain ys := by
  induction xs generalizing address with
  | nil => simp [eqAssum]
  | cons head tail ih =>
    simp only [List.cons_append, eqAssum, ih, List.length_cons]
    have addr : address + StackRemove.bytesInWord width +
        BitVec.ofNat width tail.length * StackRemove.bytesInWord width =
        address + BitVec.ofNat width (tail.length + 1) * StackRemove.bytesInWord width := by
      simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
      ac_rfl
    rw [← addr]
    exact and_assoc.symm

/-- Every finite prefix of a related nonempty block can be exposed while
retaining the parent. This is a Flapjack helper for the source block-explosion
theorem. -/
theorem memoryRel_blockExplodeTake {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (w address : BitVec width) (vars : List (Value × WordLocW width))
    (inv : memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, .word w) :: vars))
    (_low : w.getLsbD 0 = true) (real : getRealAddr conf store w = some address)
    (good : goodDimindex width) (n : Nat) :
    memoryRel conf bigEndian next refs space store memory domain
      (eqExplode (address + StackRemove.bytesInWord width) memory domain (values.take n) ++
        (.block stamp tag values, .word w) :: vars) ∧
    eqAssum (address + StackRemove.bytesInWord width) memory domain (values.take n) := by
  induction n with
  | zero => simpa [eqExplode, eqAssum] using inv
  | succ n ih =>
    by_cases bound : n < values.length
    · have takeEq : values.take (n + 1) = values.take n ++ [values[n]] := List.take_succ_eq_append_getElem bound
      have takeLen : (values.take n).length = n := by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
      have parentFirst : memoryRel conf bigEndian next refs space store memory domain
          ((.block stamp tag values, .word w) ::
            eqExplode (address + StackRemove.bytesInWord width) memory domain (values.take n) ++ vars) := by
        apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ ih.1
        intro pair member
        simp only [List.mem_cons, List.mem_append] at member ⊢
        aesop
      obtain ⟨w', addr', _, locationEq, realEq, inDomain, extended⟩ :=
        memoryRel_elAny conf bigEndian next refs space store memory domain stamp tag values (.word w)
          (eqExplode (address + StackRemove.bytesInWord width) memory domain (values.take n) ++ vars)
          n bound ⟨parentFirst, good⟩
      have sameW : w = w' := WordLocW.word.inj locationEq
      subst w'
      have sameAddress : address = addr' := Option.some.inj (real.symm.trans realEq)
      subst addr'
      rw [takeEq, eqExplode_append, eqAssum_append]
      simp only [takeLen, eqExplode, eqAssum, and_true]
      have addrEq : address + StackRemove.bytesInWord width + BitVec.ofNat width n * StackRemove.bytesInWord width =
          address + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width n := by
        rw [BitVec.mul_comm]
      rw [addrEq]
      constructor
      · apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ extended
        intro pair member
        simp only [List.mem_cons, List.mem_append] at member ⊢
        aesop
      · exact ⟨ih.2, inDomain⟩
    · have takeN : values.take n = values := List.take_of_length_le (by omega)
      have takeNext : values.take (n + 1) = values := List.take_of_length_le (by omega)
      simpa only [takeN, takeNext] using ih

/-- Every field of a related block is available at its corresponding concrete
address, and the paired fields preserve the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Block_explode"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_blockExplode {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (w address : BitVec width) (vars : List (Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, .word w) :: vars) ∧
      w.getLsbD 0 = true ∧ getRealAddr conf store w = some address ∧ goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain
      (eqExplode (address + StackRemove.bytesInWord width) memory domain values ++ vars) ∧
    eqAssum (address + StackRemove.bytesInWord width) memory domain values := by
  rintro ⟨inv, low, real, good⟩
  have exposed := memoryRel_blockExplodeTake conf bigEndian next refs space store memory domain
    stamp tag values w address vars inv low real good values.length
  simp only [List.take_length] at exposed
  refine ⟨?_, exposed.2⟩
  apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ exposed.1
  intro pair member
  simp only [List.mem_append, List.mem_cons] at member ⊢
  aesop

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
