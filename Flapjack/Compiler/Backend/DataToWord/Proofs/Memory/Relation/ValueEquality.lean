import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality
import Flapjack.Compiler.Backend.Semantics.DataSem.Stack

/-! Source-value equality with the resource count used by the word proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem
open Flapjack.SemanticPrimitivesHOL (EqResult)
open Classical
noncomputable section

mutual
/-- Count the work performed by source-value equality, retaining its errors. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "vb_eq_size_def"]
def vbEqSize {α : Type} (refs : Spt (BvlSem.Ref α)) (first second : Value) : Option (Nat × Bool) :=
  match first, second with
  | .block _ t1 xs, .block _ t2 ys =>
      if isClosure t1 xs ∨ isClosure t2 ys then
        if isClosure t1 xs ∧ isClosure t2 ys then some (1, true) else none
      else if t1 = t2 ∧ xs.length = ys.length then
        (vbEqSizeList refs xs ys).map (fun (n, b) => (n + 1, b))
      else some (1, false)
  | .refPtr b1 n1, .refPtr b2 n2 =>
      if b1 && b2 then
        match sptLookup n1 refs, sptLookup n2 refs with
        | some (.byteArray true bs1), some (.byteArray true bs2) => some (1, decide (bs1 = bs2))
        | some (.byteArray true _), _ | _, some (.byteArray true _) => none
        | _, _ => some (1, decide (n1 = n2))
      else none
  | .number n1, .number n2 => some (1, decide (n1 = n2))
  | .word64 w1, .word64 w2 => some (1, decide (w1 = w2))
  | _, _ => none
termination_by sizeOf first

/-- Count a left-to-right list comparison, stopping on the first unequal value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "vb_eq_size_def"]
def vbEqSizeList {α : Type} (refs : Spt (BvlSem.Ref α)) (first second : List Value) : Option (Nat × Bool) :=
  match first, second with
  | [], [] => some (0, true)
  | [], _ | _, [] => some (0, false)
  | x :: xs, y :: ys =>
      match vbEqSize refs x y with
      | none => none
      | some (n, false) => some (n + 1, false)
      | some (n, true) =>
          (vbEqSizeList refs xs ys).map (fun (m, b) => (m + n + 1, b))
termination_by sizeOf first
end

/-- Flapjack proof helper that discards the comparator work count. -/
def eraseCount : Option (Nat × Bool) → EqResult
  | none => .typeError
  | some (_, b) => .val b

/-- Discarding a changed count preserves the equality result (Flapjack helper). -/
theorem eraseMap (x : Option (Nat × Bool)) (f : Nat → Nat) :
    eraseCount (x.map (fun p => (f p.1,p.2))) = eraseCount x := by
  cases x with
  | none => rfl
  | some p => cases p; rfl

mutual
/-- Work-count erasure agrees with value equality (Flapjack helper). -/
theorem eraseValue {α : Type} (refs : Spt (BvlSem.Ref α)) (x y : Value) :
    eraseCount (vbEqSize refs x y) = doEq refs x y := by
  cases x <;> cases y <;> simp only [vbEqSize, doEq]
  all_goals try rfl
  case block.block s1 t1 xs s2 t2 ys =>
    by_cases hc : isClosure t1 xs ∨ isClosure t2 ys
    · simp only [hc, ite_true]
      split <;> rfl
    · simp only [hc, ite_false]
      by_cases hm : t1 = t2 ∧ xs.length = ys.length
      · simp only [hm, true_and, ite_true]
        rw [eraseMap _ (fun n => n + 1), eraseList refs xs ys]
      · simp [hm, eraseCount]
  case refPtr.refPtr b1 n1 b2 n2 =>
    split
    · split <;> simp_all [eraseCount]
    · rfl
termination_by sizeOf x

/-- Work-count erasure agrees with list equality (Flapjack helper). -/
theorem eraseList {α : Type} (refs : Spt (BvlSem.Ref α)) (xs ys : List Value) :
    eraseCount (vbEqSizeList refs xs ys) = doEqList refs xs ys := by
  cases xs <;> cases ys <;> simp only [vbEqSizeList, doEqList]
  all_goals try rfl
  case cons.cons x xs y ys =>
    have h := eraseValue refs x y
    cases he : vbEqSize refs x y with
    | none => simp [he, eraseCount] at h ⊢; rw [← h]
    | some p =>
      obtain ⟨n, b⟩ := p
      cases b
      · simp [he, eraseCount] at h
        simp [← h, eraseCount]
      · simp [he, eraseCount] at h
        simp only [← h]
        rw [eraseMap _ (fun m => m + n + 1), eraseList refs xs ys]
termination_by sizeOf xs
end

/-- Characterize successful count erasure (Flapjack helper). -/
theorem eraseCount_iff (x : Option (Nat × Bool)) (b : Bool) :
    eraseCount x = .val b ↔ ∃ n, x = some (n, b) := by
  cases x with
  | none => simp [eraseCount]
  | some p =>
    rcases p with ⟨n, c⟩
    simp [eraseCount, eq_comm]

/-- Source equality succeeds exactly when its sized comparison succeeds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "do_eq_IFF_vb_eq_size"]
theorem doEq_iff_vbEqSize {α : Type} :
    (∀ (refs : Spt (BvlSem.Ref α)) x y b,
      doEq refs x y = .val b ↔ ∃ n, vbEqSize refs x y = some (n, b)) ∧
    (∀ (refs : Spt (BvlSem.Ref α)) xs ys b,
      doEqList refs xs ys = .val b ↔ ∃ n, vbEqSizeList refs xs ys = some (n, b)) := by
  constructor
  · intro refs x y b
    rw [← eraseValue refs x y, eraseCount_iff]
  · intro refs xs ys b
    rw [← eraseList refs xs ys, eraseCount_iff]

/-- Every successful source equality comparison has a work count. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "do_eq_IMP_vb_eq_size"]
theorem doEq_imp_vbEqSize {α : Type} (refs : Spt (BvlSem.Ref α)) (x y : Value) (b : Bool) :
    doEq refs x y = .val b → ∃ n, vbEqSize refs x y = some (n, b) :=
  (doEq_iff_vbEqSize.1 refs x y b).1

/-- A successful sized comparison has the same source equality result. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "vb_eq_size_IMP_do_eq"]
theorem vbEqSize_imp_doEq {α : Type} (refs : Spt (BvlSem.Ref α)) (x y : Value) (n : Nat) (b : Bool) :
    vbEqSize refs x y = some (n, b) → doEq refs x y = .val b := by
  intro h
  exact (doEq_iff_vbEqSize.1 refs x y b).2 ⟨n, h⟩

/-- Related source values sharing a location cannot compare unequal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ptr_vb_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_ptr_vbEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (location : WordLocW width) (n : Nat) (b : Bool) (vars : List (Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((v1, location) :: (v2, location) :: vars) ∧
      vbEqSize refs v1 v2 = some (n, b) ∧ goodDimindex width → b = true := by
  rintro ⟨rel, sized, good⟩
  exact memoryRel_ptrEq conf bigEndian next refs space store memory domain v1 v2 location b vars
    ⟨rel, vbEqSize_imp_doEq refs v1 v2 n b sized, good⟩

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
