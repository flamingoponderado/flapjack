import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Full original total LASTN/drop identity, including indices beyond length.
The native suffix definition is the original reverse/take/reverse formula. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_DROP2"]
theorem lastNDrop2 {α : Type} (l : List α) (n : Nat) :
    wordSemLastN n l = l.drop (l.length-n) := by
  simp only [wordSemLastN, List.take_reverse, List.reverse_reverse]

/-- Full original length-equation decomposition. The source equation forces
nonempty input, so the head bound is derived rather than supplied as an extra
premise or replaced by an arbitrary default. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LENGTH_ID2"]
theorem lastNLengthId2 {α : Type} (stack : List α) (x : Nat) (h : x+1 = stack.length) :
    wordSemLastN (x+1) stack =
      stack.head (by intro hn; rw [hn] at h; simp at h) :: wordSemLastN x stack := by
  cases stack with
  | nil => simp at h
  | cons a ls =>
    have hx : x = ls.length := by simp only [List.length_cons] at h; omega
    simp [lastNDrop2, hx]

/-- Full original two suffix length bounds, for every list and index. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LENGTH_BOUNDS"]
theorem lastNLengthBounds {α : Type} (n : Nat) (ls : List α) :
    let xs := wordSemLastN n ls
    xs.length ≤ n ∧ xs.length ≤ ls.length := by
  simp only [wordSemLastN, List.length_reverse, List.length_take]
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

/-- Full original whole-list suffix at the successor of the tail length. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_CONS_ID"]
theorem lastNConsId {α : Type} (n : Nat) (ls : List α) (frame : α) (h : n = ls.length) :
    wordSemLastN (n+1) (frame::ls) = frame::ls := by
  simp [lastNDrop2, h]

/-- Full original EVERY transport to an actual suffix. HOL's arbitrary
predicate is a Prop predicate, and EVERY is universal list membership; no
predicate/equality instance or index guard is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVERY_IMP_EVERY_LASTN"]
theorem everyImpEveryLastN {α : Type} (xs ys : List α) (P : α → Prop) (n : Nat)
    (h : ∀ x, x ∈ xs → P x) (he : wordSemLastN n xs = ys) :
    ∀ y, y ∈ ys → P y := by
  subst ys
  rw [lastNDrop2]
  intro y hy
  exact h y (List.mem_of_mem_drop hy)

/-- Full original successor-suffix head removal. The original length guard and
whole suffix equation are both retained, including the zero-index boundary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_LESS"]
theorem lastNLess {α : Type} (ls : List α) (n : Nat) (x : α) (xs : List α)
    (hn : n+1 ≤ ls.length) (he : wordSemLastN (n+1) ls = x::xs) :
    wordSemLastN n ls = xs := by
  rw [lastNDrop2] at he ⊢
  have ht := congrArg (fun zs => zs.drop 1) he
  have hi : ls.length - (n+1) + 1 = ls.length - n := by omega
  simpa only [List.drop_drop, hi, List.drop_succ_cons, List.drop_zero] using ht

end Flapjack.WordToStackProofs
