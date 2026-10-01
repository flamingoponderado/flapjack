import Flapjack.Compiler.Backend.Parmove.StepsSem

namespace Flapjack.Compiler.Backend.Parmove

/-- Original final-state consequence of scheduler RTC preservation. All four
source premises are retained: unique destinations, real destinations, real
sources, and an actual Step closure to empty pending and active lists. This
closure is a premise of HOL's theorem; correctness of pmov producing it is
separate work, rather than an assumed algorithm simulation in this proof. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_correct"]
theorem steps_correct {α β : Type} [DecidableEq α]
    (pending emitted : List (Move α)) :
    windmill pending ∧
    (∀ move ∈ pending, move.1.isSome = true) ∧
    (∀ move ∈ pending, move.2.isSome = true) ∧
    Steps (pending, [], []) ([], [], emitted) →
      ∀ env : Option α → β,
        eqenv (parsem pending env) (seqsem emitted.reverse env) := by
  rintro ⟨unique, destinations, sources, steps⟩ env
  have valid : wf (pending, [], ([] : List (Move α))) := by
    refine ⟨?_, destinations, sources, ?_, ?_, ?_⟩
    · simpa using unique
    · simp
    · simp
    · simp [path]
  have result := steps_sem (pending, [], []) ([], [], emitted) ⟨steps, valid⟩ env
  simpa only [sem_init, sem_final] using result

end Flapjack.Compiler.Backend.Parmove
