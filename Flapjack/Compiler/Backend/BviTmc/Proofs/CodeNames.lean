module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation

@[expose] public section

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
def inputCondition {α : Type} (next : Nat) (program : List (Nat × α × Bvi.Exp)) : Prop :=
  (∀ entry ∈ program, freeNames next entry.1) ∧
  (∀ entry ∈ program, noMutcons entry.2.2) ∧
  (program.map Prod.fst).Nodup ∧
  (∀ entry ∈ program.filter (fun p => decide (Flapjack.bvlNumStubs ≤ p.1)), ¬inWorkerNamespace entry.1) ∧
  Flapjack.bvlNumStubs ≤ next ∧ inWorkerNamespace next

/-- A program with distinct labels and no mutable-block allocation satisfies
the TMC input condition when its non-stub labels are outside namespace three. -/
theorem inputCondition_of_names {α : Type} (next : Nat) (program : List (Nat × α × Bvi.Exp))
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


end Flapjack.Compiler.Backend.BviTmc
