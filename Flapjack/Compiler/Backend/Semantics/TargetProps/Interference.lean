import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Misc.ShiftSeq
import Flapjack.Misc.BytesInMemory

/-! Original machine-oracle shifts and byte-region protection. HOL sets use
predicate membership; finite FFI-entry lists and all wrapped offsets are retained. -/
namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack

@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "shift_interfer_def" (words_as_type_indexed_bitvec)]
def shiftInterfer {width : Nat} [NeZero width] {state projection : Type}
    (count : Nat) (config : MachineConfig width state projection) :
    MachineConfig width state projection :=
  { config with nextInterfer := holShiftSeq count config.nextInterfer }

@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "shift_interfer_intro" (words_as_type_indexed_bitvec)]
theorem shiftInterfer_intro {width : Nat} [NeZero width] {state projection : Type}
    (k1 k2 : Nat) (config : MachineConfig width state projection) :
    shiftInterfer k1 (shiftInterfer k2 config) = shiftInterfer (k1 + k2) config := by
  have horacle : holShiftSeq k1 (holShiftSeq k2 config.nextInterfer) =
      holShiftSeq (k1 + k2) config.nextInterfer := by
    funext index
    simp [holShiftSeq, Nat.add_assoc]
  exact congrArg (fun oracle => { config with nextInterfer := oracle }) horacle

@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "bytes_in_memory_SUBSET" (words_as_type_indexed_bitvec)]
theorem bytesInMemory_subset {width : Nat} [NeZero width]
    (p : BitVec width) (xs : List (BitVec 8)) (m : BitVec width → BitVec 8)
    (domain domain2 : BitVec width → Prop) :
    (∀ address, domain address → domain2 address) ∧ bytesInMemoryHOL p xs m domain →
      bytesInMemoryHOL p xs m domain2 := by
  intro h
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih => exact ⟨h.2.1, h.1 p h.2.2.1, ih (p + 1) ⟨h.1, h.2.2.2⟩⟩

/-- Wrapped address reassociation used in the induction. Local word arithmetic
infrastructure with no independent HOL declaration claimed. -/
private theorem advanceAddress {width : Nat} (p : BitVec width) (n : Nat) :
    (p + 1) + BitVec.ofNat width n = p + BitVec.ofNat width (n + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact congrArg (p + ·) (BitVec.add_comm _ _)

@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "bytes_in_memory_DIFF" (words_as_type_indexed_bitvec)]
theorem bytesInMemory_diff {width : Nat} [NeZero width]
    (p : BitVec width) (xs : List (BitVec 8)) (m : BitVec width → BitVec 8)
    (domain domain2 pcs : BitVec width → Prop) :
    domain = (fun address => domain2 address ∧ ¬ pcs address) ∧
      bytesInMemoryHOL p xs m domain2 ∧
      (∀ address, ¬ (pcs address ∧ ∃ offset, offset < xs.length ∧
        address = p + BitVec.ofNat width offset)) →
      bytesInMemoryHOL p xs m domain := by
  intro h
  rcases h with ⟨rfl, hmem, hdisjoint⟩
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨hmem.1, ⟨hmem.2.1, ?_⟩, ih (p + 1) hmem.2.2 ?_⟩
    · intro hpcs
      exact hdisjoint p ⟨hpcs, 0, by simp, by simp⟩
    · intro address h
      rcases h with ⟨hpcs, n, hn, heq⟩
      exact hdisjoint address ⟨hpcs, n + 1, by simpa using Nat.succ_lt_succ hn,
        heq.trans (advanceAddress p n)⟩

@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "ffi_entry_pcs_disjoint_def" (words_as_type_indexed_bitvec)]
def ffiEntryPcsDisjoint {width : Nat} [NeZero width] {state projection : Type}
    (config : MachineConfig width state projection) (s : AsmState width) (length : Nat) : Prop :=
  ∀ address, ¬ (address ∈ config.ffiEntryPcs ∧ ∃ offset, offset < length ∧
    address = s.pc + BitVec.ofNat width offset)

end Flapjack.Compiler.Backend.Semantics.TargetProps
