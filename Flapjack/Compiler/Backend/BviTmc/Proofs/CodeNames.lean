import Flapjack.Compiler.Backend.BviTmc.Proofs.Total
import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation

/-! Input and label invariants for the BVI tail-modulo-cons pass. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- A primitive operation is not mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "no_mutcons_op_def"]
def noMutconsOp (op : ClosLang.Op) : Prop :=
  ∀ tag index, op ≠ .memOp (.mutCons tag index)

/-- No expression in the tree allocates a mutable block. The list cases
quantify over their actual members, corresponding to HOL's `EVERY`. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "no_mutcons_def"]
def noMutcons (expression : Bvi.Exp) : Prop :=
  match expression with
  | .var _ | .force _ _ => True
  | .ifThenElse condition yes no => noMutcons condition ∧ noMutcons yes ∧ noMutcons no
  | .let bindings body => (∀ child : { e // e ∈ bindings }, noMutcons child.1) ∧ noMutcons body
  | .raise body | .tick body => noMutcons body
  | .call _ _ args handler =>
      (∀ child : { e // e ∈ args }, noMutcons child.1) ∧
        match handler with | none => True | some body => noMutcons body
  | .op op args => noMutconsOp op ∧ (∀ child : { e // e ∈ args }, noMutcons child.1)
  | .letCall _ _ _ args body => (∀ child : { e // e ∈ args }, noMutcons child.1) ∧ noMutcons body
  | .return args => ∀ child : { e // e ∈ args }, noMutcons child.1
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals try (have := List.sizeOf_lt_of_mem child.2; omega)
  all_goals omega

/-- A name is free when no future worker allocation can reach it. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "free_names_def"]
def freeNames (next name : Nat) : Prop :=
  ∀ k, next + Flapjack.bvlToBviNamespaces * k ≠ name

/-- The local HOL namespace-three abbreviation, represented explicitly for
the TMC pass. -/
def inWorkerNamespace (name : Nat) : Prop := name % Flapjack.bvlToBviNamespaces = 3

/-- Source program and namespace preconditions for tail-modulo-cons. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "input_condition_def"]
def inputCondition (next : Nat) (program : List (Nat × Nat × Bvi.Exp)) : Prop :=
  (∀ entry ∈ program, freeNames next entry.1) ∧
  (∀ entry ∈ program, noMutcons entry.2.2) ∧
  (program.map Prod.fst).Nodup ∧
  (∀ entry ∈ program.filter (fun p => decide (Flapjack.bvlNumStubs ≤ p.1)), ¬inWorkerNamespace entry.1) ∧
  Flapjack.bvlNumStubs ≤ next ∧ inWorkerNamespace next

/-- A program with distinct labels and no mutable-block allocation satisfies
the TMC input condition when its non-stub labels are outside namespace three. -/
theorem inputCondition_of_names (next : Nat) (program : List (Nat × Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (noMutable : ∀ entry ∈ program, noMutcons entry.2.2)
    (nextBound : Flapjack.bvlNumStubs ≤ next) (worker : inWorkerNamespace next)
    (outside : ∀ entry ∈ program, Flapjack.bvlNumStubs ≤ entry.1 → ¬inWorkerNamespace entry.1) :
    inputCondition next program := by
  refine ⟨?_, noMutable, distinct, ?_, nextBound, worker⟩
  · intro entry member k equal
    by_cases below : entry.1 < Flapjack.bvlNumStubs
    · omega
    · apply outside entry member (by omega)
      rw [← equal]
      unfold inWorkerNamespace at worker ⊢
      simpa [Nat.add_mod, Flapjack.bvlToBviNamespaces] using worker
  · intro entry member
    obtain ⟨member, above⟩ := List.mem_filter.mp member
    exact outside entry member (by simpa using above)

/-- Each generated worker advances the counter by one namespace stride.
This executable fuel-based property is not the unbounded HOL theorem port. -/
theorem compileEachFuel_next_mono (fuel next last : Nat) (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachFuel fuel next code = some (last, output)) :
    ∃ k, last = next + Flapjack.bvlToBviNamespaces * k := by
  induction code generalizing next last output with
  | nil =>
    simp [compileEachFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, by simp⟩
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    obtain ⟨decision, compiled⟩ := compileExpBounded_succeeds fuel loc next arity body
    cases decision with
    | none =>
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ := compileEachFuel_succeeds fuel next rest
      have same : (last, output) = (tailNext, (loc, arity, body) :: tailCode) := by
        have eq : some (tailNext, (loc, arity, body) :: tailCode) = some (last, output) := by
          simpa [compileEachFuel, compiled, tail] using run
        exact (Option.some.inj eq).symm
      obtain ⟨k, equal⟩ := ih next tailNext tailCode tail
      exact ⟨k, (congrArg Prod.fst same).trans equal⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ :=
        compileEachFuel_succeeds fuel (next + Flapjack.bvlToBviNamespaces) rest
      have same : (last, output) = (tailNext, (loc, arity, wrapper) :: (next, arity + 2, worker) :: tailCode) := by
        have eq : some (tailNext, (loc, arity, wrapper) :: (next, arity + 2, worker) :: tailCode) =
            some (last, output) := by simpa [compileEachFuel, compiled, tail] using run
        exact (Option.some.inj eq).symm
      obtain ⟨k, equal⟩ := ih (next + Flapjack.bvlToBviNamespaces) tailNext tailCode tail
      refine ⟨k + 1, ?_⟩
      have lastEq : last = tailNext := congrArg Prod.fst same
      rw [lastEq]
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using equal

/-- The enabled or disabled executable pass advances only by namespace
strides. This is a fuel-based helper rather than a claim of HOL correspondence. -/
theorem compileProgFuel_next_mono (fuel : Nat) (enabled : Bool) (next last : Nat)
    (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileProgFuel fuel enabled next code = some (last, output)) :
    ∃ k, last = next + Flapjack.bvlToBviNamespaces * k := by
  cases enabled with
  | false =>
    simp [compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨0, by simp⟩
  | true => exact compileEachFuel_next_mono fuel next last code output (by simpa [compileProgFuel] using run)

/-- Every emitted label is an original label or a worker allocated within
the counter interval. This concerns the executed fuel-based pass and is
untagged until correspondence with the HOL definition is established. -/
theorem compileEachFuel_mem (fuel : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (next last label : Nat) (output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachFuel fuel next code = some (last, output))
    (member : label ∈ output.map Prod.fst) :
    label ∈ code.map Prod.fst ∨
      (next ≤ label ∧ label < last ∧ ∃ k, label = next + k * Flapjack.bvlToBviNamespaces) := by
  induction code generalizing next last output with
  | nil => simp [compileEachFuel] at run; obtain ⟨_, rfl⟩ := run; simp at member
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    obtain ⟨decision, compiled⟩ := compileExpBounded_succeeds fuel loc next arity body
    cases decision with
    | none =>
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ := compileEachFuel_succeeds fuel next rest
      have equal : (tailNext, (loc, arity, body) :: tailCode) = (last, output) := by
        apply Option.some.inj
        simpa [compileEachFuel, compiled, tail] using run
      obtain ⟨rfl, rfl⟩ := equal
      simp only [List.map_cons, List.mem_cons] at member ⊢
      rcases member with same | other
      · exact Or.inl (Or.inl same)
      · rcases ih next last tailCode tail other with found | fresh
        · exact Or.inl (Or.inr found)
        · exact Or.inr fresh
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ :=
        compileEachFuel_succeeds fuel (next + Flapjack.bvlToBviNamespaces) rest
      have equal : (tailNext, (loc, arity, wrapper) :: (next, arity + 2, worker) :: tailCode) = (last, output) := by
        apply Option.some.inj
        simpa [compileEachFuel, compiled, tail] using run
      obtain ⟨rfl, rfl⟩ := equal
      have ⟨k, advance⟩ := compileEachFuel_next_mono fuel (next + Flapjack.bvlToBviNamespaces) last rest tailCode tail
      simp only [List.map_cons, List.mem_cons] at member ⊢
      rcases member with same | same | other
      · exact Or.inl (Or.inl same)
      · subst label
        right
        refine ⟨by omega, ?_, 0, by simp⟩
        have positive : 0 < Flapjack.bvlToBviNamespaces := by decide
        omega
      · rcases ih (next + Flapjack.bvlToBviNamespaces) last tailCode tail other with found | ⟨lo, hi, j, eq⟩
        · exact Or.inl (Or.inr found)
        · right
          refine ⟨by omega, hi, j + 1, ?_⟩
          simp only [Nat.add_mul, Nat.one_mul]
          omega

/-- The same output-label bound applies to the enabled or disabled
production entry point. -/
theorem compileProgFuel_mem (fuel : Nat) (enabled : Bool) (next last label : Nat)
    (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileProgFuel fuel enabled next code = some (last, output))
    (member : label ∈ output.map Prod.fst) :
    label ∈ code.map Prod.fst ∨
      (next ≤ label ∧ label < last ∧ ∃ k, label = next + k * Flapjack.bvlToBviNamespaces) := by
  cases enabled with
  | false =>
    simp [compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact Or.inl member
  | true => exact compileEachFuel_mem fuel code next last label output (by simpa [compileProgFuel] using run) member

/-- The executable TMC pass retains every original function label. -/
theorem compileEachFuel_preserves_labels (fuel : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (next last label : Nat) (output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachFuel fuel next code = some (last, output))
    (member : label ∈ code.map Prod.fst) : label ∈ output.map Prod.fst := by
  induction code generalizing next last output with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    simp only [List.map_cons, List.mem_cons] at member
    obtain ⟨decision, compiled⟩ := compileExpBounded_succeeds fuel loc next arity body
    cases decision with
    | none =>
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ := compileEachFuel_succeeds fuel next rest
      have equal : (tailNext, (loc, arity, body) :: tailCode) = (last, output) := by
        apply Option.some.inj
        simpa [compileEachFuel, compiled, tail] using run
      obtain ⟨rfl, rfl⟩ := equal
      simp only [List.map_cons, List.mem_cons]
      rcases member with same | other
      · exact Or.inl same
      · exact Or.inr (ih next last tailCode tail other)
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      obtain ⟨⟨tailNext, tailCode⟩, tail⟩ :=
        compileEachFuel_succeeds fuel (next + Flapjack.bvlToBviNamespaces) rest
      have equal : (tailNext, (loc, arity, wrapper) :: (next, arity + 2, worker) :: tailCode) = (last, output) := by
        apply Option.some.inj
        simpa [compileEachFuel, compiled, tail] using run
      obtain ⟨rfl, rfl⟩ := equal
      simp only [List.map_cons, List.mem_cons]
      rcases member with same | other
      · exact Or.inl same
      · exact Or.inr (Or.inr (ih (next + Flapjack.bvlToBviNamespaces) last tailCode tail other))

/-- Original labels survive the production entry point in either mode. -/
theorem compileProgFuel_preserves_labels (fuel : Nat) (enabled : Bool) (next last label : Nat)
    (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileProgFuel fuel enabled next code = some (last, output))
    (member : label ∈ code.map Prod.fst) : label ∈ output.map Prod.fst := by
  cases enabled with
  | false =>
    simp [compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact member
  | true =>
    exact compileEachFuel_preserves_labels fuel code next last label output (by simpa [compileProgFuel] using run) member

end Flapjack.Compiler.Backend.BviTmc
