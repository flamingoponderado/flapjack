module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.DataToWord.Variables
public import Flapjack.Misc.Option
public import Mathlib.Data.List.Induction

@[expose] public section

/-! Stack-frame relations used by data-to-word garbage-collector correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The common condition for an ordinary data frame and its word frame. This
is a factoring of the first case of `stack_rel_def`, not a HOL declaration. -/
def stackEnvRel {width : Nat} [NeZero width] (dataSize wordSize : Option Nat)
    (env : Spt DataSem.Value) (nonGc gc : List (Nat × WordLocW width)) : Prop :=
  (∀ pair ∈ gc, pair.1 ≠ 0 ∧ pair.1 % 2 = 0) ∧ dataSize = wordSize ∧
  (∀ pair ∈ nonGc, pair.1 = 0) ∧ (gc.map Prod.fst).Nodup ∧
  ∀ n, (sptLookup n env).isSome = true ↔ (sptLookup (DataToWord.adjustVar n) (sptFromAList gc)).isSome = true

/-- A data frame and word frame have corresponding sizes, handlers, live
names, and cutsets. Positive-width bit vectors represent HOL words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "stack_rel_def"
  (words_as_type_indexed_bitvec)]
def stackRel {width : Nat} [NeZero width] : DataSem.Stack → WordSemStackFrame width → Prop
  | .env size env, .stackFrame wordSize nonGc gc none => stackEnvRel size wordSize env nonGc gc
  | .exc size env handler, .stackFrame wordSize nonGc gc (some (wordHandler, _, _)) =>
      stackEnvRel size wordSize env nonGc gc ∧ wordHandler = handler
  | _, _ => False

/-- The default data global value is numeric zero when no global pointer is
installed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "the_global_def"]
def theGlobal (global : Option Nat) : DataSem.Value :=
  (global.map (DataSem.Value.refPtr true)).getD (.number 0)

/-- Check the return location stored under key zero in a word frame's
non-GC cutset, using HOL's first-match association lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "contains_loc_def"
  (words_as_type_indexed_bitvec)]
def containsLoc {width : Nat} [NeZero width] : WordSemStackFrame width → Nat × Nat → Prop
  | .stackFrame _ nonGc _ _, (l1, l2) => sptAListLookup 0 nonGc = some (.loc l1 l2)

/-- Match even, nonzero word local names with their corresponding data local.
HOL's `THE` is retained even for a missing lookup, where its result is
unspecified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "join_env_def"]
noncomputable def joinEnv {α β : Type} [Nonempty α] (env : Spt α)
    (values : List (Nat × β)) : List (α × β) :=
  (values.filter fun pair => pair.1 ≠ 0 ∧ pair.1 % 2 = 0).map fun (name, value) =>
    (holThe (sptLookup ((name - 2) / 2) env), value)

/-- Flatten paired data and word stacks, stopping at the shorter list and
ignoring frame handlers, as in the source relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "flat_def"
  (words_as_type_indexed_bitvec)]
noncomputable def flatStack {width : Nat} [NeZero width] :
    List DataSem.Stack → List (WordSemStackFrame width) → List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)
  | .env _ env :: rest, .stackFrame _ _ values _ :: frames => @joinEnv DataSem.Value (WordLocW width) ⟨.number 0⟩ env values ++ flatStack rest frames
  | .exc _ env _ :: rest, .stackFrame _ _ values _ :: frames => @joinEnv DataSem.Value (WordLocW width) ⟨.number 0⟩ env values ++ flatStack rest frames
  | _, _ => []

/-- Flattening paired stacks distributes over append when the first stacks
have the same length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "flat_APPEND"
  (words_as_type_indexed_bitvec)]
theorem flatStack_append {width : Nat} [NeZero width]
    (xs : List DataSem.Stack) (ys : List (WordSemStackFrame width))
    (xs1 : List DataSem.Stack) (ys1 : List (WordSemStackFrame width))
    (sameLength : xs.length = ys.length) :
    flatStack (xs ++ xs1) (ys ++ ys1) = flatStack xs ys ++ flatStack xs1 ys1 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [flatStack]
    | cons y ys => simp at sameLength
  | cons x xs ih =>
    cases ys with
    | nil => simp at sameLength
    | cons y ys =>
      have lengths : xs.length = ys.length := by simpa using sameLength
      cases x <;> cases y <;> simp [flatStack, ih ys lengths, List.append_assoc]

/-- Related data and word stacks have exactly the same optional accounted
size, including exception-frame overhead. -/
theorem stackRel_sizeOfStack {width : Nat} [NeZero width]
    {source : List DataSem.Stack} {target : List (WordSemStackFrame width)}
    (related : List.Forall₂ stackRel source target) :
    wordSemStackSize target = DataSem.sizeOfStack source := by
  induction related with
  | nil => rfl
  | @cons frame wordFrame rest wordRest head tail ih =>
    have frameSize : wordSemStackSizeFrame wordFrame = DataSem.sizeOfStackFrame frame := by
      cases wordFrame with
      | stackFrame wordSize nonGc gc handler =>
        cases frame with
        | env size env =>
          cases handler with
          | none => simpa [stackRel, stackEnvRel, wordSemStackSizeFrame, DataSem.sizeOfStackFrame] using head.2.1.symm
          | some info => simp [stackRel] at head
        | exc size env saved =>
          cases handler with
          | none => simp [stackRel] at head
          | some info =>
            obtain ⟨h, a, b⟩ := info
            simp only [stackRel] at head
            simp [wordSemStackSizeFrame, DataSem.sizeOfStackFrame, head.1.2.1]
    change wordSemOptionAdd (wordSemStackSizeFrame wordFrame) (wordSemStackSize wordRest) =
      Option.map₂ (· + ·) (DataSem.sizeOfStackFrame frame) (DataSem.sizeOfStack rest)
    rw [frameSize, ih]
    cases DataSem.sizeOfStackFrame frame <;> cases DataSem.sizeOfStack rest <;> rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
