module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Timestamps

@[expose] public section

/-!
# Set equations for `all_ts`

Counterparts of `all_ts_cons`, `all_ts_in_no_block`, `all_ts_append` and
`all_ts_head` in `cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
Sets are predicates: HOL `x INSERT s` is `fun t => t = x ∨ s t`, `s ∪ t` is
`fun x => s x ∨ t x`, and `t ∈ s` is `s t`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `all_ts_cons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_cons"]
theorem allTimestamps_cons :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (stack : List Flapjack.Compiler.Backend.DataSem.Value) (ts tag : Nat)
      (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      allTimestamps refs (.block ts tag xs :: stack) = fun t => t = ts ∨ allTimestamps refs (xs ++ stack) t := by
  intro refs stack ts tag xs
  funext t
  apply propext
  simp only [allTimestamps, List.mem_cons, List.mem_append]
  constructor
  · rintro ⟨value, (inRefs | rfl | inStack), stamp⟩
    · exact Or.inr ⟨value, Or.inl inRefs, stamp⟩
    · simp only [valueTimestamps, List.mem_cons, List.mem_flatMap] at stamp
      rcases stamp with rfl | ⟨child, member, childStamp⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨child, Or.inr (Or.inl member), childStamp⟩
    · exact Or.inr ⟨value, Or.inr (Or.inr inStack), stamp⟩
  · rintro (rfl | ⟨value, (inRefs | inXs | inStack), stamp⟩)
    · exact ⟨.block t tag xs, Or.inr (Or.inl rfl), by simp [valueTimestamps]⟩
    · exact ⟨value, Or.inl inRefs, stamp⟩
    · refine ⟨.block ts tag xs, Or.inr (Or.inl rfl), ?_⟩
      simp only [valueTimestamps, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨value, inXs, stamp⟩
    · exact ⟨value, Or.inr (Or.inr inStack), stamp⟩

/-- HOL `all_ts_in_no_block`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_in_no_block"]
theorem allTimestamps_in_noBlock :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (stack : List Flapjack.Compiler.Backend.DataSem.Value) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (t : Nat),
      (∀ ts tag xs, v ≠ .block ts tag xs) ∧ allTimestamps refs (v :: stack) t → allTimestamps refs stack t := by
  rintro refs stack v t ⟨nonblock, member⟩
  rwa [allTimestamps_consNoBlock refs stack v nonblock] at member

/-- HOL `all_ts_append`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_append"]
theorem allTimestamps_append :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (x y : List Flapjack.Compiler.Backend.DataSem.Value),
      allTimestamps refs (x ++ y) = fun t => allTimestamps refs x t ∨ allTimestamps refs y t := by
  intro refs x y
  funext t
  apply propext
  simp only [allTimestamps, List.mem_append]
  constructor
  · rintro ⟨value, (inRefs | inX | inY), stamp⟩
    · exact Or.inl ⟨value, Or.inl inRefs, stamp⟩
    · exact Or.inl ⟨value, Or.inr inX, stamp⟩
    · exact Or.inr ⟨value, Or.inr inY, stamp⟩
  · rintro (⟨value, (inRefs | inX), stamp⟩ | ⟨value, (inRefs | inY), stamp⟩)
    · exact ⟨value, Or.inl inRefs, stamp⟩
    · exact ⟨value, Or.inr (Or.inl inX), stamp⟩
    · exact ⟨value, Or.inl inRefs, stamp⟩
    · exact ⟨value, Or.inr (Or.inr inY), stamp⟩

/-- HOL `all_ts_head`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_head"]
theorem allTimestamps_head :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (x : Flapjack.Compiler.Backend.DataSem.Value) (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      allTimestamps refs (x :: xs) = fun t => allTimestamps refs [x] t ∨ allTimestamps refs xs t := by
  intro refs x xs
  exact allTimestamps_append refs [x] xs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
