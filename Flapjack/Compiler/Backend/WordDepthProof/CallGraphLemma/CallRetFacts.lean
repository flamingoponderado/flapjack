import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallUnfold

/-!
# `max_depth_call_graph_lemma`: frame facts for the returning `Call`

Flapjack infrastructure for the returning-call part of the `Call` case, as in
the HOL proof's uses of `push_env_def`, `pop_env_def`, `evaluate_stack_swap`,
`s_key_eq_stack_size` and `LASTN_LEMMA`.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact WordSemStackEq

/-- The frame pushed by `push_env` and the fields it changes. -/
theorem pushEnv_facts {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (st : WordSemStateFiniteExact width C F) :
    ∃ l0 l, (pushEnv envs handler st).stack =
        .stackFrame st.localsSize l0 l (handler.map fun h => (st.handler, h.2.2.1, h.2.2.2)) ::
          st.stack ∧
      (pushEnv envs handler st).stackMax =
        wordSemOptionMax st.stackMax (wordSemStackSize (pushEnv envs handler st).stack) ∧
      (pushEnv envs handler st).stackSize = st.stackSize ∧
      (pushEnv envs handler st).localsSize = st.localsSize ∧
      (pushEnv envs handler st).code = st.code ∧
      (handler.isSome = true → (pushEnv envs handler st).handler = st.stack.length) := by
  rcases hl : wordSemEnvToList envs.2 st.permute with ⟨l, perm⟩
  cases handler with
  | none => exact ⟨sptToAList envs.1, l, by simp [pushEnv, hl]⟩
  | some h =>
      obtain ⟨a, b, c, e⟩ := h
      exact ⟨sptToAList envs.1, l, by simp [pushEnv, hl]⟩

/-- `stack_size` of a pushed frame. -/
theorem stackSize_cons {width : Nat} [NeZero width] (fr : WordSemStackFrame width)
    (xs : List (WordSemStackFrame width)) :
    wordSemStackSize (fr :: xs) = wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize xs) := by
  simp [wordSemStackSize]

/-- After a run whose stack is key-equal to `fr :: st`, popping restores the
frame's `locals_size` and a stack of the same `stack_size` as `st`. -/
theorem pop_after_keyEq {width : Nat} [NeZero width] {C F : Type}
    (m : Option Nat) (l0 : List (Nat × WordLocW width)) (l : List (Nat × WordLocW width))
    (h : Option (Nat × Nat × Nat)) (st : List (WordSemStackFrame width))
    (t p : WordSemStateFiniteExact width C F)
    (hkey : sKeyEq (.stackFrame m l0 l h :: st) t.stack) (hp : popEnv t = some p) :
    p.localsSize = m ∧ wordSemStackSize p.stack = wordSemStackSize st := by
  rcases hts : t.stack with _ | ⟨fr, rest⟩
  · rw [hts] at hkey; simp [sKeyEq] at hkey
  rw [hts] at hkey
  obtain ⟨m', e0, e, h'⟩ := fr
  simp only [sKeyEq] at hkey
  obtain ⟨hrest, hfr⟩ := hkey
  have hm : m = m' := by
    cases h <;> cases h' <;> simp only [sFrameKeyEq] at hfr <;> tauto
  unfold popEnv at hp
  rw [hts] at hp
  cases h' with
  | none =>
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hm.symm, (sKeyEqStackSize _ _ hrest).symm⟩
  | some y =>
      obtain ⟨y1, y2, y3⟩ := y
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hm.symm, (sKeyEqStackSize _ _ hrest).symm⟩

end Flapjack.Compiler.Backend.WordDepthProof
