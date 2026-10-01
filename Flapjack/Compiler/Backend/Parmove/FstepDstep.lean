import Flapjack.Compiler.Backend.Parmove.DSteps
import Flapjack.Compiler.Backend.Parmove.SplitSource

namespace Flapjack.Compiler.Backend.Parmove

/-- The actual deterministic scheduler takes one primitive deterministic step
on every nonterminal state. No well-formedness or search certificate is assumed. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_dstep"]
theorem fstepDstep {α : Type} [DecidableEq α] (state : State α)
    (unfinished : ∀ emitted, state ≠ ([], [], emitted)) :
    DStep state (fstep state) := by
  obtain ⟨pending, active, emitted⟩ := state
  cases active with
  | nil =>
    cases pending with
    | nil => exact False.elim (unfinished emitted rfl)
    | cons move pending =>
      obtain ⟨d, s⟩ := move
      by_cases same : s = d
      · subst s
        simpa [fstep] using DStep.removeSelf d pending emitted
      · simpa [fstep, same] using DStep.start d s pending emitted same
  | cons move active =>
    obtain ⟨d, s⟩ := move
    cases suffix : (splitSource d pending).2 with
    | cons next rest =>
      obtain ⟨r, v⟩ := next
      have matchSource := splitSource_suffix_match d pending (r,v) rest suffix
      dsimp at matchSource
      subst v
      have step := DStep.extend d r s (splitSource d pending).1 rest active emitted
        (splitSource_prefix_noRead d pending)
      have partition := splitSource_append d pending
      rw [suffix] at partition
      simpa [fstep, suffix, List.append_assoc, partition] using step
    | nil =>
      have noRead := (splitSource_suffix_nil_iff d pending).mp suffix
      cases active with
      | nil => simpa [fstep, suffix] using DStep.emitLast d s pending emitted noRead
      | cons head tail =>
        have front := frontLast_append head tail
        by_cases cycle : (frontLast head tail).2.2 = d
        · have step := DStep.saveEmit d s (frontLast head tail).2.1 pending
            (frontLast head tail).1 emitted noRead
          have lastPair : ((frontLast head tail).2.1, d) = (frontLast head tail).2 :=
            Prod.ext rfl cycle.symm
          simpa [fstep, suffix, cycle, lastPair, front] using step
        · have step := DStep.emitHead (frontLast head tail).2.1 d
            (frontLast head tail).2.2 s pending (frontLast head tail).1 emitted
            noRead (Ne.symm cycle)
          simpa [fstep, suffix, cycle, front] using step

end Flapjack.Compiler.Backend.Parmove
