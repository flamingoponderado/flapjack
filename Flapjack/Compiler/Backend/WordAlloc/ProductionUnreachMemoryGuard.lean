import Flapjack.RiscV.WordDeadCode

namespace Flapjack.WordAlloc
open RiscV

/-- Actual sequence pruning and Move merging retain support of both inputs.
The extra production guard has no HOL original. -/
private theorem unreachSequenceMemoryGuard {α : Type} (first second : WordProg α)
    (left : allocatorMemorySupported first = true)
    (right : allocatorMemorySupported second = true) :
    allocatorMemorySupported (wordCopyUnreachSeq first second) = true := by
  unfold wordCopyUnreachSeq
  repeat' (split <;> simp_all [allocatorMemorySupported])

private theorem unreachFoldMemoryGuard {α : Type} (pieces : List (WordProg α))
    (supported : ∀ piece ∈ pieces, allocatorMemorySupported piece = true) :
    allocatorMemorySupported (pieces.foldr wordCopyUnreachSeq .skip) = true := by
  induction pieces with
  | nil => simp [allocatorMemorySupported]
  | cons first rest ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at supported
      exact unreachSequenceMemoryGuard first _ supported.1 (ih supported.2)

/-- Complete suffix-accumulator flattening retains supported pieces, including
both returning Call bodies and the unchanged nonreturning handler. Flapjack
production-domain infrastructure, not a HOL evaluator theorem. -/
private theorem unreachPartsMemoryGuard {α : Type} (program : WordProg α)
    (suffix : List (WordProg α)) (supported : allocatorMemorySupported program = true)
    (suffixSupported : ∀ piece ∈ suffix, allocatorMemorySupported piece = true) :
    ∀ piece ∈ wordCopyUnreachPartsAcc program suffix, allocatorMemorySupported piece = true := by
  fun_induction wordApplyColour (fun name => name) program generalizing suffix <;>
    simp_all [wordCopyUnreachPartsAcc, allocatorMemorySupported]
  case case8 => solve_by_elim
  all_goals try constructor
  all_goals apply unreachFoldMemoryGuard
  all_goals apply_assumption
  all_goals simp

/-- Complete executed post-copy unreachable elimination retains input memory
support. Dropped tails can remove unsupported instructions, so equality is
not asserted. No output-support or target-run premise is assumed; this
additional runtime-domain fact has no HOL original. -/
theorem unreachMemoryGuard {α : Type} (program : WordProg α)
    (supported : allocatorMemorySupported program = true) :
    allocatorMemorySupported (wordRemoveUnreachableAfterCopy program) = true := by
  apply unreachFoldMemoryGuard
  exact unreachPartsMemoryGuard program [] supported (by simp)

end Flapjack.WordAlloc
