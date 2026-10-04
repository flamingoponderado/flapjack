import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Motive
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap

/-!
# `max_depth_call_graph_lemma`: `Alloc` case

As in HOL (`gc_const`, `pop_env_const`, `gc_s_key_eq`): the frame pushed for
the collection raises `stack_max` by `locals_size + stack_size stack`, the
collector keeps `stack_max`/`stack_size` and the frame keys, and popping it
restores `locals_size`.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact WordSemStackEq

namespace CallGraphLemmaAllocWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaAllocWitnesses

open CallGraphLemmaAllocWitnesses

/-- `option_le` arithmetic for the `Alloc` frame (Flapjack infrastructure). -/
theorem alloc_bound (m ss g l : Option Nat) :
    optionLe (wordSemOptionMax m (wordSemOptionAdd l ss))
      (optionMap₂ max m (optionMap₂ (· + ·) ss (optionMap₂ max g (optionMap₂ (· + ·) l (some 0))))) := by
  rcases m with _ | m <;> rcases ss with _ | ss <;> rcases g with _ | g <;> rcases l with _ | l <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe]
  all_goals omega

/-- The successful collection-and-pop of `alloc`: the popped state keeps the
caller's `locals_size` and `stack_size`, and its `stack_max` is the pushed
state's (Flapjack infrastructure). -/
theorem alloc_pop_facts {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (s g q : WordSemStateFiniteExact width C F)
    (hg : gc (pushEnv envs none s) = some g) (hq : popEnv g = some q) :
    q.stackMax = wordSemOptionMax s.stackMax (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack)) ∧
      q.stackSize = s.stackSize ∧ q.localsSize = s.localsSize := by
  have gc1 := gcConst _ _ hg
  have pq := popEnvConst _ _ hq
  have hkey := gcSKeyEq _ _ hg
  rcases hl : wordSemEnvToList envs.2 s.permute with ⟨l, perm⟩
  have hpush : pushEnv envs none s =
      { s with stack := .stackFrame s.localsSize (sptToAList envs.1) l none :: s.stack,
               stackMax := wordSemOptionMax s.stackMax
                 (wordSemStackSize (.stackFrame s.localsSize (sptToAList envs.1) l none :: s.stack)),
               permute := perm } := by
    simp only [pushEnv, hl]
  rw [hpush] at gc1 hkey
  refine ⟨?_, ?_, ?_⟩
  · rw [pq.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, gc1.2.2.2.2.2.2.2.2.2.2.2.1]
    simp [wordSemStackSize, wordSemStackSizeFrame]
  · rw [pq.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, gc1.2.2.2.2.2.2.2.2.2.2.2.2]
  · -- the collector keeps the pushed frame's `locals_size`, which `pop_env` restores
    rcases hgs : g.stack with _ | ⟨fr, rest⟩
    · rw [hgs] at hkey; simp [sKeyEq] at hkey
    rw [hgs] at hkey
    obtain ⟨m, e0, e, hd⟩ := fr
    simp only [sKeyEq] at hkey
    cases hd with
    | some y => simp [sFrameKeyEq] at hkey
    | none =>
        have hm : s.localsSize = m := by
          simp only [sFrameKeyEq] at hkey
          tauto
        unfold popEnv at hq
        rw [hgs] at hq
        simp only [Option.some.injEq] at hq
        subst hq
        exact hm.symm

/-- `max_depth_call_graph_lemma`, `Alloc` case. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraphLemma_Alloc {width : Nat} [NeZero width] {C F : Type}
    (n' : Nat) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    depthPost (.alloc n' names) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  simp only [callGraph, maxDepth]
  rcases hv : WordSemStateFiniteExact.getVar n' s with _ | ⟨w⟩ | ⟨a, b⟩
  · exact absurd (by rw [evaluate, hv]) herr
  swap
  · exact absurd (by rw [evaluate, hv]) herr
  have hev : evaluate (.alloc n' names) s = alloc w names s := by rw [evaluate, hv]
  rw [hev] at herr ⊢
  unfold alloc at herr ⊢
  rcases he : wordSemCutEnvs names s.locals with _ | envs
  · simp only [he] at herr; exact absurd rfl herr
  simp only [he] at herr ⊢
  rcases hg : gc (pushEnv envs none (setStore .allocSize (.word w) s)) with _ | g
  · simp only [hg] at herr; exact absurd rfl herr
  simp only [hg] at herr ⊢
  rcases hq : popEnv g with _ | q
  · simp only [hq] at herr; exact absurd rfl herr
  simp only [hq] at herr ⊢
  obtain ⟨hmax, hss, hls⟩ := alloc_pop_facts envs _ g q hg hq
  have hmax' : q.stackMax = wordSemOptionMax s.stackMax
      (wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack)) := by
    rw [hmax, ← hloc]; rfl
  have hbound : optionLe q.stackMax (optionMap₂ max s.stackMax
      (optionMap₂ (· + ·) (wordSemStackSize s.stack)
        (optionMap₂ max (maxDepthGraphs s.stackSize ns ns funs funs2)
          (optionMap₂ (· + ·) (sptLookup n s.stackSize) (some 0))))) := by
    rw [hmax']; exact alloc_bound _ _ _ _
  rcases hst : getStore .allocSize q with _ | ws
  · simp only [hst] at herr; exact absurd rfl herr
  simp only [hst] at herr ⊢
  rcases hsp : hasSpace ws q with _ | _ | _
  · simp only [hsp] at herr; exact absurd rfl herr
  · exact ⟨hbound, fun _ => ⟨hss, fun h => by simp at h⟩⟩
  · exact ⟨hbound, fun _ => ⟨hss, fun _ => hls⟩⟩

end Flapjack.Compiler.Backend.WordDepthProof
