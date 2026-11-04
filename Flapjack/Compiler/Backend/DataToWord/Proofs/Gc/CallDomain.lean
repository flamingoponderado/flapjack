import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnv
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcFrames
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap

/-! Domain preservation when returning to a saved word-language frame. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack WordSemStackEq

/-- If a GC association list has the saved environment's keys, restoring it
with the non-GC list yields exactly the union of the two cut domains. -/
theorem savedFrame_domain {width : Nat} [NeZero width]
    (env1 env2 : Spt (WordLocW width)) (perm : Nat → Nat → Nat)
    (gc : List (Nat × WordLocW width))
    (keys : gc.map Prod.fst = (wordSemEnvToList env2 perm).1.map Prod.fst) :
    sptDomainEqUnion (sptUnion (sptFromAList gc) (sptFromAList (sptToAList env1))) env1 env2 := by
  have gcDomain : sptDomain (sptFromAList gc) = sptDomain env2 := by
    funext key
    apply propext
    rw [sptDomainFromAList, keys]
    simp only [List.mem_map]
    constructor
    · rintro ⟨⟨k, value⟩, member, equal⟩
      simp only at equal
      subst k
      have inEnv := (wordSemEnvToList_mem_iff env2 perm (key, value)).mp member
      exact (sptMem_iff_lookup key env2).mpr ⟨value, (sptMemToAList env2 key value).mp inEnv⟩
    · intro present
      obtain ⟨value, found⟩ := (sptMem_iff_lookup key env2).mp present
      refine ⟨(key, value), ?_, rfl⟩
      exact (wordSemEnvToList_mem_iff env2 perm (key, value)).mpr ((sptMemToAList env2 key value).mpr found)
  intro key
  rw [sptMem_sptUnion]
  have gcMem : sptMem key (sptFromAList gc) ↔ sptMem key env2 := by
    change sptDomain (sptFromAList gc) key ↔ sptDomain env2 key
    rw [gcDomain]
  have nonGcMem : sptMem key (sptFromAList (sptToAList env1)) ↔ sptMem key env1 := by
    simp [sptMem_iff_lookup, sptLookup_sptFromAList_sptToAList]
  rw [gcMem, nonGcMem, or_comm]

/-- A result-producing evaluation retains the keys of the top saved frame;
popping that frame restores exactly the original cut domains. -/
theorem evaluate_popEnv_domain {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (env1 env2 : Spt (WordLocW width)) (args : List (WordLocW width)) (size : Option Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (loc : WordLocW width) (values : List (WordLocW width))
    (post popped : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) handler (WordSemStateFiniteExact.decClock state))) =
          (some (.result loc values), post))
    (pop : WordSemStateFiniteExact.popEnv post = some popped) :
    sptDomainEqUnion popped.locals env1 env2 := by
  let entered := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (env1, env2) handler (WordSemStateFiniteExact.decClock state))
  have keys := evaluateStackSwap prog entered
  change WordSemStateFiniteExact.evaluate prog entered = (some (.result loc values), post) at run
  unfold stackSwapPost at keys
  rw [run] at keys
  have keys := keys.1
  have initialStack : entered.stack =
      .stackFrame state.localsSize (sptToAList env1) (wordSemEnvToList env2 state.permute).1
        (handler.map fun (_, _, a, b) => (state.handler, a, b)) :: state.stack := by
    cases handler with
    | none => rfl
    | some info => obtain ⟨a, b, c, d⟩ := info; rfl
  rw [initialStack] at keys
  cases postStack : post.stack with
  | nil => simp [sKeyEq, postStack] at keys
  | cons frame rest =>
    rw [postStack] at keys
    have frameKey := keys.2
    cases frame with
    | stackFrame size' nonGc gc saved =>
      have frameFacts := (sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp frameKey
      have gcKeys := frameFacts.1.symm
      have nonGcEq := frameFacts.2.2.1
      cases saved with
      | none =>
        simp [WordSemStateFiniteExact.popEnv, postStack] at pop
        subst popped
        simpa [nonGcEq] using savedFrame_domain env1 env2 state.permute gc gcKeys
      | some info =>
        obtain ⟨h, a, b⟩ := info
        simp [WordSemStateFiniteExact.popEnv, postStack] at pop
        subst popped
        simpa [nonGcEq] using savedFrame_domain env1 env2 state.permute gc gcKeys

/-- An exception caught by the freshly pushed handler restores locals with
exactly the original cut domains, even if GC changed their values. -/
theorem evaluate_exception_domain {width : Nat} [NeZero width] {C F : Type}
    (prog handlerBody : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (env1 env2 : Spt (WordLocW width)) (args : List (WordLocW width)) (size : Option Nat)
    (name a b : Nat) (loc value : WordLocW width) (post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b))
          (WordSemStateFiniteExact.decClock state))) = (some (.exception loc value), post)) :
    sptDomainEqUnion post.locals env1 env2 := by
  let entered := WordSemStateFiniteExact.callEnv args size
    (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b)) (WordSemStateFiniteExact.decClock state))
  have facts := evaluateStackSwap prog entered
  change WordSemStateFiniteExact.evaluate prog entered = (some (.exception loc value), post) at run
  unfold stackSwapPost at facts
  rw [run] at facts
  obtain ⟨_, nonGc, gc, saved, rest, frameSize, gcAfter, stackAt, _, keys, _, _⟩ := facts
  have initialStack : entered.stack =
      .stackFrame state.localsSize (sptToAList env1) (wordSemEnvToList env2 state.permute).1
        (some (state.handler, a, b)) :: state.stack := rfl
  have handlerEq : entered.handler = state.stack.length := rfl
  rw [initialStack, handlerEq, wordSemLastN_eq_drop] at stackAt
  simp only [List.length_cons] at stackAt
  simp only [Nat.sub_self, List.drop_zero, List.cons.injEq, WordSemStackFrame.stackFrame.injEq, Option.some.injEq] at stackAt
  obtain ⟨⟨frameSizeEq, nonGcEq, gcEq, savedEq⟩, _⟩ := stackAt
  subst nonGc
  subst gc
  obtain ⟨gcKeys, localsEq⟩ := keys
  rw [localsEq]
  exact savedFrame_domain env1 env2 state.permute gcAfter gcKeys.symm

/-- The return-domain result also holds after the caller's clock clamp. -/
theorem evaluate_fixClock_popEnv_domain {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (env1 env2 : Spt (WordLocW width)) (args : List (WordLocW width)) (size : Option Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (loc : WordLocW width) (values : List (WordLocW width)) (post popped : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.fixClock
      (WordSemStateFiniteExact.callEnv args size (WordSemStateFiniteExact.pushEnv (env1, env2) handler (WordSemStateFiniteExact.decClock state)))
      (WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) handler (WordSemStateFiniteExact.decClock state)))) =
          (some (.result loc values), post))
    (pop : WordSemStateFiniteExact.popEnv post = some popped) :
    sptDomainEqUnion popped.locals env1 env2 := by
  cases evalRun : WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (env1, env2) handler (WordSemStateFiniteExact.decClock state))) with
  | mk result last =>
    simp [evalRun, WordSemStateFiniteExact.fixClock] at run
    obtain ⟨resultEq, postEq⟩ := run
    subst result
    subst post
    have popOriginal : WordSemStateFiniteExact.popEnv last = some { popped with clock := last.clock, termdep := last.termdep } := by
      cases stackEq : last.stack with
      | nil => simp [WordSemStateFiniteExact.popEnv, stackEq] at pop
      | cons frame rest =>
        cases frame with
        | stackFrame n nonGc gc saved =>
          cases saved with
          | none =>
            simp only [WordSemStateFiniteExact.popEnv, stackEq, Option.some.injEq] at pop
            subst popped
            simp [WordSemStateFiniteExact.popEnv, stackEq]
          | some info =>
            obtain ⟨h, a, b⟩ := info
            simp only [WordSemStateFiniteExact.popEnv, stackEq, Option.some.injEq] at pop
            subst popped
            simp [WordSemStateFiniteExact.popEnv, stackEq]
    have h := evaluate_popEnv_domain prog state env1 env2 args size handler loc values last _ evalRun popOriginal
    exact h

/-- The caught-exception domain result is unaffected by clock clamping. -/
theorem evaluate_fixClock_exception_domain {width : Nat} [NeZero width] {C F : Type}
    (prog handlerBody : WordLangProgHOL (BitVec width)) (state : WordSemStateFiniteExact width C F)
    (env1 env2 : Spt (WordLocW width)) (args : List (WordLocW width)) (size : Option Nat)
    (name a b : Nat) (loc value : WordLocW width) (post : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.fixClock
      (WordSemStateFiniteExact.callEnv args size (WordSemStateFiniteExact.pushEnv (env1, env2)
        (some (name, handlerBody, a, b)) (WordSemStateFiniteExact.decClock state)))
      (WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b))
          (WordSemStateFiniteExact.decClock state)))) = (some (.exception loc value), post)) :
    sptDomainEqUnion post.locals env1 env2 := by
  cases evalRun : WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args size
      (WordSemStateFiniteExact.pushEnv (env1, env2) (some (name, handlerBody, a, b))
        (WordSemStateFiniteExact.decClock state))) with
  | mk result last =>
    simp [evalRun, WordSemStateFiniteExact.fixClock] at run
    obtain ⟨resultEq, postEq⟩ := run
    subst result
    subst post
    exact evaluate_exception_domain prog handlerBody state env1 env2 args size name a b loc value last evalRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
