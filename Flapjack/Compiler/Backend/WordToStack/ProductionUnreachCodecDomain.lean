import Flapjack.RiscV.WordDeadCode
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

namespace Flapjack
open WordProgCarrierCodec
open RiscV

/-- Actual sequence pruning/merge closure. Both input domains are established
independently, and unreachable tails may be discarded. Flapjack-only helper. -/
private theorem sequenceDomain {width : Nat} (first second : WordProg (BitVec width))
    (left : supportsCodec first = true) (right : supportsCodec second = true) :
    supportsCodec (wordCopyUnreachSeq first second) = true := by
  unfold wordCopyUnreachSeq
  repeat' (split <;> simp_all [supportsCodec])

/-- Actual fold closure on accepted pieces. Flapjack-only carrier helper. -/
private theorem foldDomain {width : Nat} (pieces : List (WordProg (BitVec width)))
    (accepted : ∀ piece ∈ pieces, supportsCodec piece = true) :
    supportsCodec (pieces.foldr wordCopyUnreachSeq .skip) = true := by
  induction pieces with
  | nil => simp [supportsCodec]
  | cons first rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at accepted
    exact sequenceDomain first _ accepted.1 (ih accepted.2)

/-- Full actual suffix-accumulator flattening closure, including both returning
Call bodies and an unchanged nonreturning handler. Flapjack-only helper. -/
private theorem partsDomain {width : Nat} (program : WordProg (BitVec width))
    (suffix : List (WordProg (BitVec width)))
    (accepted : supportsCodec program = true)
    (suffixAccepted : ∀ piece ∈ suffix, supportsCodec piece = true) :
    ∀ piece ∈ wordCopyUnreachPartsAcc program suffix, supportsCodec piece = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing suffix <;>
    simp_all [wordCopyUnreachPartsAcc, supportsCodec]
  case case8 => solve_by_elim
  all_goals try constructor
  all_goals apply foldDomain
  all_goals apply_assumption
  all_goals simp

/-- Actual executed post-copy unreachable elimination preserves native codec
acceptance. Unreachable rejected primitives can disappear, so the result is
one-way. No normal-form, output-codec, memory-guard, termination or successful-
pass premise is assumed. Flapjack-only infrastructure, not a HOL theorem port. -/
theorem wordLangProgToHOL_wordRemoveUnreachableAfterCopy_isSome {width : Nat}
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveUnreachableAfterCopy program)).isSome = true := by
  rw [codecDomain] at accepted ⊢
  apply foldDomain
  exact partsDomain program [] accepted (by simp)

end Flapjack
