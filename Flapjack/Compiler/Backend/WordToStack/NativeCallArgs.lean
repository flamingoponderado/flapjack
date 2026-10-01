import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

/-! Native call destination and argument-frame helpers for Word-to-Stack.
The source Call compiler clauses require native HolProg results. These literal
helpers preserve the source empty-argument branch, and do not establish call
simulation or route the production compiler through the native compiler.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open WordToStackRegFormat (wReg2)

/-- Literal slot movement in the source recursive order; the body is retained
at zero and the higher slots are copied before the current slot. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "stack_move_def"
  (words_as_type_indexed_bitvec)]
def stackMoveNative {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) : HolProg width :=
  match n with
  | 0 => p
  | n + 1 =>
    .seq (stackMoveNative n (start + 1) offset i p)
      (.seq (.stackLoad i (start + offset)) (.stackStore i start))

/-- Literal argument allocation and frame-slot movement on the native carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "StackArgs_def"
  (words_as_type_indexed_bitvec)]
def stackArgsNative {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (argCount : Nat) (kf : Nat × Nat × Nat) : HolProg width :=
  let n := WordToStack.stackArgCount dest argCount kf.1
  stackMoveNative n 0 kf.2.1 kf.1 (.stackAlloc n)

/-- Literal direct/indirect destination dispatch. HOL explicitly chooses the
raise stub for empty indirect arguments. LAST is accessed only after the source
LENGTH=0 guard proves nonemptiness, with no external success or bounds premise. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "call_dest_def"
  (words_as_type_indexed_bitvec)]
def callDestNative {width : Nat} [NeZero width]
    (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    HolProg width × Sum Nat Nat :=
  match pos with
  | some p => (.skip, .inl p)
  | none =>
    if h : args.length = 0 then (.skip, .inl Flapjack.raiseStubLocation)
    else
      let last := args.getLast (by intro hnil; subst args; simp at h)
      let w := wReg2 last kf
      (wStackLoadNative w.1 .skip, .inr w.2)

/-- Flapjack-only all-input representation transport, with arbitrary native
body program. There is no HOL declaration for this payload codec relation. -/
theorem toGeneric_stackMoveNative {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    toGeneric (stackMoveNative n start offset i p) =
      WordToStackRegFormat.stackMove n start offset i (toGeneric p) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simpa [stackMoveNative, WordToStackRegFormat.stackMove, toGeneric, Prog.map] using
      congrArg (fun q : ProgM (BitVec width) =>
        StackLang.Prog.seq q (.seq (.stackLoad i (start + offset)) (.stackStore i start)))
        (ih (start + 1))

/-- Flapjack-only argument-frame representation transport, not a simulation. -/
theorem toGeneric_stackArgsNative {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (argCount : Nat) (kf : Nat × Nat × Nat) :
    toGeneric (stackArgsNative (width := width) dest argCount kf) =
      WordToStackRegFormat.stackArgs (γ := BitVec width) dest argCount kf := by
  simp only [stackArgsNative, WordToStackRegFormat.stackArgs, toGeneric_stackMoveNative]
  simp [toGeneric, Prog.map]

/-- Flapjack-only universal dispatch representation transport; both the native
program and the returned destination are related without a target-result premise. -/
theorem toGeneric_callDestNative {width : Nat} [NeZero width]
    (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    (toGeneric (callDestNative (width := width) pos args kf).1,
      (callDestNative (width := width) pos args kf).2) =
      WordToStackRegFormat.callDest (α := BitVec width) pos args kf := by
  cases pos with
  | some p => simp [callDestNative, WordToStackRegFormat.callDest, toGeneric, Prog.map]
  | none =>
    by_cases hnil : args = []
    · subst args
      simp [callDestNative, WordToStackRegFormat.callDest, toGeneric, Prog.map]
    · have hlen : args.length ≠ 0 := by simpa using hnil
      simp only [callDestNative, dif_neg hlen, WordToStackRegFormat.callDest,
        List.getLast?_eq_some_getLast hnil, toGeneric_wStackLoad]
      simp [toGeneric, Prog.map]

end Flapjack.Compiler.Backend.WordToStack.Native
