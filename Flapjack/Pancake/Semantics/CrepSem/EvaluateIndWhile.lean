import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

namespace Flapjack

/-- Flapjack-specific induction interface, with no standalone HOL original.
Specializes the exact evaluator's well-founded induction to the guarded While
recursive calls printed in `crep_sem_evaluate_ind_probe.out`. The body and
NONE/Continue-0 re-entry hypotheses are separate and use the plain source
states. Other constructors retain the well-founded step obligation. This is
not the full HOL `evaluate_ind` port: it uses Lean sizeOf and does not state
HOL's other constructor clauses. No recursive correctness fact is assumed
outside an induction handler. -/
theorem evalCrepSemHOLProgExact_inductWhile {width : Nat} [NeZero width] {σ : Type}
    {motive : CrepProgHOL width → CrepSemHOLState width σ → Prop}
    (hother : ∀ (program : CrepProgHOL width) (state : CrepSemHOLState width σ),
      (∀ condition body, program ≠ .while condition body) →
      (∀ program' state',
        Prod.Lex Nat.lt Nat.lt (state'.clock, sizeOf program')
          (state.clock, sizeOf program) → motive program' state') →
      motive program state)
    (hwhile : ∀ condition body (state : CrepSemHOLState width σ),
      (∀ (w : BitVec width),
        evalCrepSemHOLExp state condition = some (.word w) →
        w ≠ 0 → state.clock ≠ 0 → motive body (decClockCrepSemHOL state)) →
      (∀ (w : BitVec width) result (post : CrepSemHOLState width σ),
        evalCrepSemHOLExp state condition = some (.word w) →
        w ≠ 0 → state.clock ≠ 0 →
        evalCrepSemHOLProgExact (decClockCrepSemHOL state) body = (result, post) →
        (result = none ∨ result = some (.continue 0)) →
        motive (.while condition body) post) →
      motive (.while condition body) state) :
    ∀ program state, motive program state := by
  apply evalCrepSemHOLProgExact_inductLex
  intro program state ih
  cases program with
  | «while» condition body =>
      apply hwhile condition body state
      · intro w _ _ hclock
        apply ih body (decClockCrepSemHOL state)
        rw [Prod.lex_def]
        left
        change state.clock - 1 < state.clock
        exact Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega)
      · intro w result post _ _ hclock hrun _
        have hbound : post.clock ≤ (decClockCrepSemHOL state).clock := by
          have h := evalCrepSemHOLProg_clock_le (decClockCrepSemHOL state)
            (fun a => Classical.propDecidable ((decClockCrepSemHOL state).memaddrs a))
            (fun a => Classical.propDecidable ((decClockCrepSemHOL state).shMemaddrs a)) body
          rw [← evalCrepSemHOLProgExact_eq_core] at h
          rw [hrun] at h
          exact h
        apply ih (.while condition body) post
        rw [Prod.lex_def]
        left
        exact Nat.lt_of_le_of_lt hbound
          (Nat.sub_lt (Nat.pos_of_ne_zero hclock) (by omega))
  | _ =>
      apply hother _ state
      · intro condition body heq
        cases heq
      · exact ih

end Flapjack
