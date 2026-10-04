import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation

/-!
# Word-to-Stack allocation simulation

The allocation-store and `alloc` unfolding lemmas of
`word_to_stackProofScript.sml` (1600-1611, 2075-2101) used by the `Alloc` case
of `comp_correct`.
-/

namespace Flapjack.WordToStackProofs.AllocSimulation
open Flapjack.Compiler.Encoders.Asm Flapjack.WordSemStateFiniteExact

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Canonical source-state codec re-export for the WordSem evaluator carrier
(`fmap_as_finite_support` on `alloc_alt`); no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

theorem fmap_ext {α β : Type} {m1 m2 : HolFiniteMapExact α β}
    (h : ∀ key, m1.lookup key = m2.lookup key) : m1 = m2 := by
  rcases m1 with ⟨l1, _⟩
  rcases m2 with ⟨l2, _⟩
  have : l1 = l2 := funext h
  subst this
  rfl

/-- Exact HOL `state_rel_set_store_0` (`word_to_stackProofScript.sml:1600-1611`).
Both stores receive the same `AllocSize` entry; frame sizes are `0`, while
`len` and `extra` stay arbitrary. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelSetStore0 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (s5 : WordSemStateFiniteExact width (Nat × C) F)
    (t5 : StackSemStateFiniteExact width C F) (len : List Nat) (extra : Nat)
    (w : WordLocW width) :
    stateRel ac k 0 0 s5 t5 len extra →
      stateRel ac k 0 0 (setStore .allocSize w s5)
        (StackSemStateOps.setStore .allocSize w t5) len extra := by
  intro h
  unfold stateRel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38⟩ := h
  have hhandler : (t5.store.updateEq (WordStore.allocSize, w)).lookup .handler =
      t5.store.lookup .handler := by
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15, h16, ?_, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, ?_⟩
  · show s5.store.updateEq (WordStore.allocSize, w) =
      (t5.store.updateEq (WordStore.allocSize, w)).eraseEq .handler
    rw [h12]
    apply fmap_ext
    intro key
    by_cases hk : key = .handler
    · subst hk; simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL]
    · by_cases ha : key = .allocSize
      · subst ha
        simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL]
      · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL, hk, ha]
  · show (t5.store.updateEq (WordStore.allocSize, w)).lookup .handler ≠ none
    rw [hhandler]; exact h17
  · show (stackRel k s5.handler s5.stack
        ((t5.store.updateEq (WordStore.allocSize, w)).lookup .handler) _ _ _ len ∧ _)
    rw [hhandler]
    exact h38

/-- Exact HOL `alloc_alt` (`word_to_stackProofScript.sml:2075-2101`). The
source configuration carrier is `Nat × C` as in HOL; HOL `push_env env NONE s
with <|locals := LN; locals_size := SOME 0|>` updates the pushed state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allocAlt {width : Nat} [NeZero width] {C F : Type}
    (c : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width (Nat × C) F) :
    (alloc c names s).1 ≠ some .error →
      alloc c names s =
        match wordSemCutEnvs names s.locals with
        | none => (some .error, s)
        | some env =>
            match gc (setStore .allocSize (.word c)
                ({ pushEnv env none s with locals := .ln, localsSize := some 0 })) with
            | none => (some .error, s)
            | some s' =>
                match popEnv s' with
                | none => (some .error, s')
                | some s' =>
                    match getStore .allocSize s' with
                    | none => (some .error, s')
                    | some w =>
                        match hasSpace w s' with
                        | none => (some .error, s')
                        | some true => (none, s')
                        | some false => (some .notEnoughSpace, flushState true s') := by
  intro h
  unfold alloc at h ⊢
  rcases hcut : wordSemCutEnvs names s.locals with _ | env
  · simp [hcut] at h
  simp only [hcut] at h ⊢
  simp only [gc, pushEnv, setStore] at h ⊢
  generalize s.gcFun _ = g at h ⊢
  rcases g with _ | ⟨wl, m, st⟩
  · simp at h
  simp only at h ⊢
  generalize wordSemDecStack wl _ = d at h ⊢
  rcases d with _ | stack
  · simp at h
  simp only [popEnv] at h ⊢
  rcases stack with _ | ⟨⟨m', e0, e, handler⟩, xs⟩
  · simp at h
  rcases handler with _ | ⟨n, _, _⟩ <;> rfl

end Flapjack.WordToStackProofs.AllocSimulation
