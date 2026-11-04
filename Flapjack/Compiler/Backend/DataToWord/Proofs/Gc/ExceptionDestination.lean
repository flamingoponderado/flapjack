import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcFrames
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackLists

/-! Exception-handler destinations through word evaluation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack WordSemStackEq

/-- States with key-equivalent stacks and equal handler indices choose the
same exception destination. The restored values may differ. -/
theorem jumpExc_destination_of_keyEq {width : Nat} [NeZero width] {C F : Type}
    (before after next : WordSemStateFiniteExact width C F) (a b : Nat)
    (keys : sKeyEq before.stack after.stack) (handler : after.handler = before.handler)
    (jump : WordSemStateFiniteExact.jumpExc after = some (next, a, b)) :
    ∃ beforeNext, WordSemStateFiniteExact.jumpExc before = some (beforeNext, a, b) := by
  have lengths := sKeyEqLength _ _ keys
  have reverseKeys := (sKeyEqSym _ _).mp keys
  unfold WordSemStateFiniteExact.jumpExc at jump
  split at jump
  · rename_i valid
    have beforeValid : before.handler < before.stack.length := by omega
    cases suffix : wordSemLastN (after.handler + 1) after.stack with
    | nil => simp [suffix] at jump
    | cons frame rest =>
      cases frame with
      | stackFrame size nonGc gc saved =>
        cases saved with
        | none => simp [suffix] at jump
        | some info =>
          obtain ⟨saved, label1, label2⟩ := info
          simp [suffix] at jump
          obtain ⟨rfl, rfl, rfl⟩ := jump
          obtain ⟨gc', rest', beforeSuffix, _, _⟩ :=
            sKeyEqLastNExists after.stack before.stack (after.handler + 1) size nonGc gc
              (saved, label1, label2) rest ⟨reverseKeys, suffix⟩
          rw [handler] at beforeSuffix
          refine ⟨{ before with handler := saved, locals := sptUnion (sptFromAList gc') (sptFromAList nonGc), stack := rest', localsSize := size }, ?_⟩
          simp [WordSemStateFiniteExact.jumpExc, beforeValid, beforeSuffix]
  · simp at jump

/-- A continuing word computation preserves the destination of any later
exception jump, including after the sequence clock clamp. -/
theorem evaluate_continue_jumpExc_destination {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (before after next : WordSemStateFiniteExact width C F)
    (a b : Nat) (run : WordSemStateFiniteExact.evaluate prog before = (none, after))
    (jump : WordSemStateFiniteExact.jumpExc after = some (next, a, b)) :
    ∃ beforeNext, WordSemStateFiniteExact.jumpExc before = some (beforeNext, a, b) := by
  have swap := evaluateStackSwap prog before
  unfold stackSwapPost at swap
  rw [run] at swap
  exact jumpExc_destination_of_keyEq before after next a b swap.1 swap.2.1 jump

/-- Entering a tail call leaves the current exception destination unchanged. -/
theorem callEnv_jumpExc_destination {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F) (args : List (WordLocW width)) (size : Option Nat)
    (a b : Nat) (jump : WordSemStateFiniteExact.jumpExc
      (WordSemStateFiniteExact.callEnv args size (WordSemStateFiniteExact.decClock state)) = some (next, a, b)) :
    ∃ beforeNext, WordSemStateFiniteExact.jumpExc state = some (beforeNext, a, b) := by
  apply jumpExc_destination_of_keyEq state (WordSemStateFiniteExact.callEnv args size (WordSemStateFiniteExact.decClock state)) next a b
  · exact of_eq_true (sKeyEqRefl state.stack)
  · rfl
  · exact jump

/-- The exception destination immediately after installing a handler is its
specified label pair. -/
theorem pushCall_jumpExc_destination {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) (env1 env2 : Spt (WordLocW width))
    (args : List (WordLocW width)) (size : Option Nat) (name a b : Nat)
    (handlerBody : WordLangProgHOL (BitVec width)) :
    ∃ next, WordSemStateFiniteExact.jumpExc
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b))
          (WordSemStateFiniteExact.decClock state))) = some (next, a, b) := by
  let entered := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b)) (WordSemStateFiniteExact.decClock state))
  have stack : entered.stack = .stackFrame state.localsSize (sptToAList env1)
      (wordSemEnvToList env2 state.permute).1 (some (state.handler, a, b)) :: state.stack := rfl
  have handler : entered.handler = state.stack.length := rfl
  have valid : entered.handler < entered.stack.length := by rw [handler, stack]; simp
  have suffix : wordSemLastN (entered.handler + 1) entered.stack =
      .stackFrame state.localsSize (sptToAList env1) (wordSemEnvToList env2 state.permute).1
        (some (state.handler, a, b)) :: state.stack := by
    rw [handler, stack, wordSemLastN_eq_drop]
    simp
  refine ⟨{ entered with handler := state.handler, locals := sptUnion (sptFromAList (wordSemEnvToList env2 state.permute).1) (sptFromAList (sptToAList env1)), stack := state.stack, localsSize := state.localsSize }, ?_⟩
  change WordSemStateFiniteExact.jumpExc entered = _
  simp [WordSemStateFiniteExact.jumpExc, valid, suffix]

/-- An exception jump from a call with an ordinary saved frame selects the
same outer handler as the caller did before pushing that frame. -/
theorem pushCall_noHandler_jumpExc_destination {width : Nat} [NeZero width] {C F : Type}
    (state next : WordSemStateFiniteExact width C F) (env1 env2 : Spt (WordLocW width))
    (args : List (WordLocW width)) (size : Option Nat) (a b : Nat)
    (jump : WordSemStateFiniteExact.jumpExc
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock state))) = some (next, a, b)) :
    ∃ beforeNext, WordSemStateFiniteExact.jumpExc state = some (beforeNext, a, b) := by
  let entered := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock state))
  have stack : entered.stack = .stackFrame state.localsSize (sptToAList env1)
      (wordSemEnvToList env2 state.permute).1 none :: state.stack := rfl
  have handler : entered.handler = state.handler := rfl
  change WordSemStateFiniteExact.jumpExc entered = some (next, a, b) at jump
  unfold WordSemStateFiniteExact.jumpExc at jump
  split at jump
  · rename_i valid
    have le : state.handler ≤ state.stack.length := by rw [handler, stack] at valid; simp only [List.length_cons] at valid; omega
    have beforeValid : state.handler < state.stack.length := by
      by_contra notLt
      have equal : state.handler = state.stack.length := by omega
      rw [handler, stack, equal, wordSemLastN_eq_drop] at jump
      simp at jump
    have suffixEq : wordSemLastN (entered.handler + 1) entered.stack = wordSemLastN (state.handler + 1) state.stack := by
      rw [handler, stack, wordSemLastN_eq_drop, wordSemLastN_eq_drop]
      simp only [List.length_cons]
      have difference : state.stack.length + 1 - (state.handler + 1) =
          (state.stack.length - (state.handler + 1)) + 1 := by omega
      rw [difference]
      rfl
    rw [suffixEq] at jump
    cases suffix : wordSemLastN (state.handler + 1) state.stack with
    | nil => simp [suffix] at jump
    | cons frame rest =>
      cases frame with
      | stackFrame frameSize nonGc gc saved =>
        cases saved with
        | none => simp [suffix] at jump
        | some info =>
          obtain ⟨oldHandler, label1, label2⟩ := info
          simp [suffix] at jump
          obtain ⟨rfl, rfl, rfl⟩ := jump
          refine ⟨{ state with handler := oldHandler, locals := sptUnion (sptFromAList gc) (sptFromAList nonGc), stack := rest, localsSize := frameSize }, ?_⟩
          simp [WordSemStateFiniteExact.jumpExc, beforeValid, suffix]
  · simp at jump

/-- Propagating an exception through an ordinary saved frame leaves fewer
frames than the caller originally had. -/
theorem evaluate_noHandler_exception_stack_shorter {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (state post : WordSemStateFiniteExact width C F)
    (env1 env2 : Spt (WordLocW width)) (args : List (WordLocW width)) (size : Option Nat)
    (loc value : WordLocW width)
    (run : WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock state))) =
        (some (.exception loc value), post))
    (outerValid : state.handler < state.stack.length) : post.stack.length < state.stack.length := by
  let entered := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock state))
  have facts := evaluateStackSwap prog entered
  change WordSemStateFiniteExact.evaluate prog entered = (some (.exception loc value), post) at run
  unfold stackSwapPost at facts
  rw [run] at facts
  obtain ⟨_, nonGc, gc, saved, rest, frameSize, gcAfter, stackAt, _, _, tailKeys, _, _⟩ := facts
  have stack : entered.stack = .stackFrame state.localsSize (sptToAList env1)
      (wordSemEnvToList env2 state.permute).1 none :: state.stack := rfl
  have handler : entered.handler = state.handler := rfl
  have sizeEq := congrArg List.length stackAt
  rw [handler, stack, wordSemLastN_eq_drop] at sizeEq
  simp only [List.length_cons, List.length_drop] at sizeEq
  have tailLength := sKeyEqLength _ _ tailKeys
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
