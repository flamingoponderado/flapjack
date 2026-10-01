import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

/-! Deterministic parallel-move scheduling, counterpart of
`compiler/backend/reg_alloc/parmoveScript.sml`. `none` is the temporary register.
The scheduler uses the original decreasing measure; its semantic correctness
and executed compiler wiring remain separate open ports. -/

namespace Flapjack.Compiler.Backend.Parmove

abbrev Move (α : Type) := Option α × Option α
abbrev State (α : Type) := List (Move α) × List (Move α) × List (Move α)

/-- Flapjack infrastructure specializing HOL's indexed `splitAtPki` to the
index-independent source-equality predicate used by `fstep`. The prefix ends
immediately before the first matching source; the suffix retains that move.
This is not a port of the general indexed HOL list combinator. -/
def splitSource {α : Type} [DecidableEq α] (destination : Option α) :
    List (Move α) → List (Move α) × List (Move α)
  | [] => ([], [])
  | move :: moves =>
      if move.2 = destination then ([], move :: moves)
      else
        let result := splitSource destination moves
        (move :: result.1, result.2)

theorem splitSource_append {α : Type} [DecidableEq α]
    (destination : Option α) (moves : List (Move α)) :
    (splitSource destination moves).1 ++ (splitSource destination moves).2 = moves := by
  induction moves with
  | nil => rfl
  | cons move moves ih =>
      simp only [splitSource]
      split
      · rfl
      · simpa using congrArg (List.cons move) ih

/-- Total nonempty-list decomposition used to implement HOL's `FRONT`/`LAST`
without adding an arbitrary default register or a nonemptiness premise. -/
def frontLast {α : Type} (head : Move α) :
    List (Move α) → List (Move α) × Move α
  | [] => ([], head)
  | next :: rest =>
      let result := frontLast next rest
      (head :: result.1, result.2)

theorem frontLast_length {α : Type} (head : Move α) (tail : List (Move α)) :
    (frontLast head tail).1.length = tail.length := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih => simpa [frontLast] using congrArg Nat.succ (ih next)

theorem frontLast_append {α : Type} (head : Move α) (tail : List (Move α)) :
    (frontLast head tail).1 ++ [(frontLast head tail).2] = head :: tail := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih => simpa [frontLast] using congrArg (List.cons head) (ih next)

/-- HOL's deterministic step, including the first-source search and the cycle
save through the temporary register. Equality uses Lean propositional equality;
`DecidableEq` supplies computation, with no `BEq` correctness premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "fstep_def"]
def fstep {α : Type} [DecidableEq α] : State α → State α
  | ([], [], emitted) => ([], [], emitted)
  | ((destination, source) :: pending, [], emitted) =>
      if source = destination then (pending, [], emitted)
      else (pending, [(destination, source)], emitted)
  | (pending, (destination, source) :: active, emitted) =>
      let result := splitSource destination pending
      match result.2 with
      | next :: rest => (result.1 ++ rest, next :: (destination, source) :: active, emitted)
      | [] =>
          match active with
          | [] => (pending, [], (destination, source) :: emitted)
          | head :: tail =>
              let last := frontLast head tail
              if last.2.2 = destination then
                (pending, last.1 ++ [(last.2.1, none)],
                  (destination, source) :: (none, destination) :: emitted)
              else (pending, active, (destination, source) :: emitted)

/-- Flapjack termination infrastructure for the literal `pmov` recursion.
The measure is the one used in HOL's `pmov_def` termination proof. -/
def measure {α : Type} (state : State α) : Nat :=
  2 * state.1.length + state.2.1.length

theorem fstep_decreases {α : Type} [DecidableEq α]
    (pending active emitted : List (Move α))
    (unfinished : pending ≠ [] ∨ active ≠ []) :
    measure (fstep (pending, active, emitted)) < measure (pending, active, emitted) := by
  cases active with
  | nil =>
      cases pending with
      | nil => simp at unfinished
      | cons move pending =>
          rcases move with ⟨destination, source⟩
          simp only [fstep]
          split <;> simp [measure] <;> omega
  | cons move active =>
      rcases move with ⟨destination, source⟩
      have length := congrArg List.length (splitSource_append destination pending)
      simp only [List.length_append] at length
      simp only [fstep]
      cases suffix : (splitSource destination pending).2 with
      | cons next rest =>
          simp only [suffix, List.length_cons] at length
          simp [measure]
          omega
      | nil =>
          simp only
          cases active with
          | nil => simp [measure]
          | cons head tail =>
              simp only
              split <;> simp [measure, frontLast_length]

/-- Literal HOL scheduler recursion. The final state is preserved, including its
emitted moves; all other states recurse through the reviewed deterministic step.
No fuel limit or well-formedness restriction is added. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_def"]
def pmov {α : Type} [DecidableEq α] (state : State α) : State α :=
  if _finished : state.1 = [] ∧ state.2.1 = [] then state
  else pmov (fstep state)
termination_by measure state
decreasing_by
  rcases state with ⟨pending, active, emitted⟩
  apply fstep_decreases
  by_cases hp : pending = []
  · right
    intro ha
    exact _finished ⟨hp, ha⟩
  · exact Or.inl hp

/-- HOL's wrapper lifts registers to SOME, schedules, and reverses the emitted
moves. NONE denotes the temporary register in the result. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_def"]
def parmove {α : Type} [DecidableEq α] (moves : List (α × α)) : List (Move α) :=
  (pmov (moves.map (fun move => (some move.1, some move.2)), [], [])).2.2.reverse

end Flapjack.Compiler.Backend.Parmove
