import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma

/-!
# `max_depth_call_graph` and `max_depth_Call_NONE`

`word_depthProofScript.sml:790-806` and `857-880`: the full-call-graph
corollaries of `max_depth_call_graph_lemma`, the latter for a tail call to a
named function (used by the Pancake-to-target proof).
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphWitnesses

open CallGraphWitnesses

/-- Arithmetic of `max_depth_call_graph` (Flapjack infrastructure). -/
theorem full_graph_bound (m sz l d t : Option Nat)
    (h : optionLe t (optionMap₂ max m (optionMap₂ (· + ·) sz
      (optionMap₂ max (optionMap₂ max l (optionMap₂ max d (some 0))) d)))) :
    optionLe t (optionMap₂ max m (optionMap₂ (· + ·) sz
      (optionMap₂ max (optionMap₂ (· + ·) l (some 0)) d))) := by
  rcases m with _ | m <;> rcases sz with _ | sz <;> rcases l with _ | l <;>
    rcases d with _ | d <;> rcases t with _ | t <;>
    simp only [optionMap₂, optionLe] at h ⊢
  all_goals omega

/-- Arithmetic of `max_depth_Call_NONE` (Flapjack infrastructure). -/
theorem call_none_bound (m sz l d t : Option Nat)
    (h : optionLe t (optionMap₂ max (wordSemOptionMax m (wordSemOptionAdd sz l))
      (optionMap₂ (· + ·) sz (optionMap₂ max (optionMap₂ (· + ·) l (some 0)) d)))) :
    optionLe t (optionMap₂ max m (optionMap₂ (· + ·) sz
      (optionMap₂ max (optionMap₂ (· + ·) l (some 0)) d))) := by
  rcases m with _ | m <;> rcases sz with _ | sz <;> rcases l with _ | l <;>
    rcases d with _ | d <;> rcases t with _ | t <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe] at h ⊢
  all_goals omega

/-- Full original `max_depth_call_graph` (`word_depthProofScript.sml:790-806`):
`!prog s res s1 funs n a. evaluate (prog, s) = (res,s1) /\ subspt funs s.code /\
lookup n funs = SOME (a,prog) /\ s.locals_size = lookup n s.stack_size /\
res <> SOME Error ==> option_le s1.stack_max (OPTION_MAP2 MAX s.stack_max
(OPTION_MAP2 (+) (stack_size s.stack) (max_depth s.stack_size (full_call_graph n funs))))`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_call_graph"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallGraph {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
      (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (n a : Nat),
      evaluate prog s = (res, s1) ∧ sptSubspt funs s.code ∧ sptLookup n funs = some (a, prog) ∧
        s.localsSize = sptLookup n s.stackSize ∧ res ≠ some .error →
      optionLe s1.stackMax
        (optionMap₂ max s.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize s.stack)
            (maxDepth s.stackSize (fullCallGraph n funs)))) := by
  intro prog s res s1 funs n a ⟨hev, hcode, hl, hloc, herr⟩
  have h := (maxDepthCallGraphLemma prog s res s1 funs n [n] funs
    ⟨hev, (sptSubsptLookup funs funs).mpr fun _ _ h => h, hcode, hloc, herr,
      List.mem_singleton_self _, by simp, by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; simp [hl]⟩).1
  simp only [maxDepthGraphs, hl] at h
  simp only [fullCallGraph, hl, maxDepth]
  exact full_graph_bound _ _ _ _ _ h

/-- Full original `max_depth_Call_NONE` (`word_depthProofScript.sml:857-880`):
`evaluate (Call NONE (SOME dest) args NONE, s) = (res,s1) /\ res <> SOME Error /\
subspt funs s.code ==> option_le s1.stack_max (OPTION_MAP2 MAX s.stack_max
(OPTION_MAP2 (+) (stack_size s.stack) (max_depth s.stack_size (full_call_graph dest funs))))`,
with its free variables universally bound. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_Call_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallNONE {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (args : List Nat) (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :
    evaluate (.call none (some dest) args none) s = (res, s1) ∧ res ≠ some .error ∧
        sptSubspt funs s.code →
      optionLe s1.stackMax
        (optionMap₂ max s.stackMax
          (optionMap₂ (· + ·) (wordSemStackSize s.stack)
            (maxDepth s.stackSize (fullCallGraph dest funs)))) := by
  rintro ⟨hev, herr, hcode⟩
  rcases hl : sptLookup dest funs with _ | ⟨a, body⟩
  · simp only [fullCallGraph, hl, maxDepth]
    rw [optionMap2_none_right, optionMap2_none_right]
    trivial
  simp only [fullCallGraph, hl, maxDepth]
  have hc := subspt_lookup_some hcode hl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at hev
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hbad : ¬ wordSemBadDestArgs (some dest) args = true := by simp [wordSemBadDestArgs]
  simp only [hg, hbad, Bool.false_eq_true, if_false] at hev
  rcases hf : wordSemFindCode (some dest) (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  obtain ⟨⟨a', hcd⟩, hss, -⟩ := findCode_some_dest hf
  rw [hcd] at hc
  cases hc
  subst hss
  simp only [hf] at hev
  by_cases hz : s.clock = 0
  · simp only [hz, ↓reduceIte, Prod.mk.injEq] at hev
    obtain ⟨-, rfl⟩ := hev
    exact (optionLe_X_MAX_X _ _).2
  simp only [hz, ↓reduceIte] at hev
  rcases hr : evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (decClock s)) with ⟨r, t⟩
  rw [hr] at hev
  dsimp only at hev
  by_cases hb : wordSemBadFunReturn r = true
  · simp only [hb, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at hev
  obtain ⟨rfl, rfl⟩ := hev
  have h := maxDepthCallGraph body _ _ _ funs dest a
    ⟨hr, hcode, hl, rfl, herr⟩
  simp only [fullCallGraph, hl, maxDepth] at h
  exact call_none_bound _ _ _ _ _ h

end Flapjack.Compiler.Backend.WordDepthProof
