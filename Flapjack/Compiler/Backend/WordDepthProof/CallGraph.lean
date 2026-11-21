module

public import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma

@[expose] public section

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

/-- Arithmetic of `max_depth_Call_SOME` (Flapjack infrastructure). -/
theorem call_some_bound (m L S Ld X t : Option Nat)
    (h : optionLe t (optionMap₂ max
      (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd L S))
        (wordSemOptionAdd (wordSemOptionAdd L S) Ld))
      (optionMap₂ (· + ·) (wordSemOptionAdd L S) (optionMap₂ max (optionMap₂ (· + ·) Ld (some 0)) X)))) :
    optionLe t (optionMap₂ max m (optionMap₂ (· + ·) L (optionMap₂ (· + ·) S
      (optionMap₂ max (optionMap₂ (· + ·) Ld (some 0)) X)))) := by
  rcases m with _ | m <;> rcases L with _ | L <;> rcases S with _ | S <;> rcases Ld with _ | Ld <;>
    rcases X with _ | X <;> rcases t with _ | t <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe] at h ⊢
  all_goals omega

/-- Timeout arithmetic of `max_depth_Call_SOME` (Flapjack infrastructure). -/
theorem call_some_timeout_bound (m L S Ld X : Option Nat) :
    optionLe (wordSemOptionMax (wordSemOptionMax m (wordSemOptionAdd L S))
        (wordSemOptionAdd (wordSemOptionAdd L S) Ld))
      (optionMap₂ max m (optionMap₂ (· + ·) L (optionMap₂ (· + ·) S
        (optionMap₂ max (optionMap₂ (· + ·) Ld (some 0)) X)))) := by
  rcases m with _ | m <;> rcases L with _ | L <;> rcases S with _ | S <;> rcases Ld with _ | Ld <;>
    rcases X with _ | X <;>
    simp only [wordSemOptionMax, wordSemOptionAdd, optionMap₂, optionLe]
  all_goals omega

/-- Full original `max_depth_Call_SOME` (`word_depthProofScript.sml:808-855`):
`evaluate (Call (SOME (n1,n2,Skip,n3,n4)) (SOME dest) args NONE, s) = (res,s1) /\
res <> SOME Error /\ subspt funs s.code ==> option_le s1.stack_max
(OPTION_MAP2 MAX s.stack_max (OPTION_MAP2 (+) s.locals_size (OPTION_MAP2 (+)
(stack_size s.stack) (max_depth s.stack_size (full_call_graph dest funs)))))`,
with its free variables explicit. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_Call_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem maxDepthCallSOME {width : Nat} [NeZero width] {C F : Type}
    (n1 : List Nat) (n2 : WordLangCutsetsHOL) (n3 n4 dest : Nat) (args : List Nat)
    (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) :
    evaluate (.call (some (n1, n2, WordLangProgHOL.skip, n3, n4)) (some dest) args none) s = (res, s1) ∧
        res ≠ some .error ∧ sptSubspt funs s.code →
      optionLe s1.stackMax
        (optionMap₂ max s.stackMax
          (optionMap₂ (· + ·) s.localsSize
            (optionMap₂ (· + ·) (wordSemStackSize s.stack)
              (maxDepth s.stackSize (fullCallGraph dest funs))))) := by
  rintro ⟨hev, herr, hcode⟩
  rcases hl : sptLookup dest funs with _ | ⟨a, body⟩
  · simp only [fullCallGraph, hl, maxDepth]
    rw [optionMap2_none_right, optionMap2_none_right, optionMap2_none_right]
    trivial
  simp only [fullCallGraph, hl, maxDepth]
  have hc := subspt_lookup_some hcode hl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at hev
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hbad : ¬ wordSemBadDestArgs (some dest) args = true := by simp [wordSemBadDestArgs]
  simp only [hg, hbad, Bool.false_eq_true, if_false] at hev
  split at hev
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  rename_i args1 prog ss hf
  obtain ⟨⟨a', hcd⟩, hss, -⟩ := findCode_some_dest hf
  rw [hcd] at hc
  cases hc
  subst hss
  by_cases hnames : sptDomainEmpty n2.1 ∨ ¬ n1.Nodup
  · simp only [hnames, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  simp only [hnames, if_false] at hev
  rcases he : wordSemCutEnvs n2 s.locals with _ | envs
  · simp only [he, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  simp only [he] at hev
  obtain ⟨l0, l, hst0, hmax0, -, -, -, -⟩ := pushEnv_facts envs none s
  have hc0 : (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none s)).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack)))
        (wordSemOptionAdd (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack))
          (sptLookup dest s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs none s).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs none s).stack) (sptLookup dest s.stackSize)) = _
    rw [hmax0, hst0, stackSize_cons]
    simp [wordSemStackSizeFrame]
  by_cases hz : s.clock = 0
  · simp only [hz, ↓reduceIte, Prod.mk.injEq] at hev
    obtain ⟨-, rfl⟩ := hev
    show optionLe (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none s)).stackMax _
    rw [hc0]
    exact call_some_timeout_bound _ _ _ _ _
  simp only [hz, ↓reduceIte] at hev
  obtain ⟨l0', l', hst1, hmax1, hss1, -, hcode1, -⟩ := pushEnv_facts envs none (decClock s)
  have hcs : (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none (decClock s))).stack = .stackFrame s.localsSize l0' l' none :: s.stack := hst1
  have hcStack : wordSemStackSize (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none (decClock s))).stack =
      wordSemOptionAdd s.localsSize (wordSemStackSize s.stack) := by
    rw [hcs, stackSize_cons]; simp [wordSemStackSizeFrame]
  have hcMax : (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none (decClock s))).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack)))
        (wordSemOptionAdd (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack))
          (sptLookup dest s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs none (decClock s)).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs none (decClock s)).stack)
        (sptLookup dest s.stackSize)) = _
    rw [hmax1, hst1, stackSize_cons]
    simp [wordSemStackSizeFrame, decClock]
  rcases hcv : evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none (decClock s))) with ⟨rc, t⟩
  rw [hcv] at hev
  -- the callee's run satisfies `max_depth_call_graph`
  have hcallee : rc ≠ some .error → optionLe t.stackMax
      (optionMap₂ max s.stackMax (optionMap₂ (· + ·) s.localsSize
        (optionMap₂ (· + ·) (wordSemStackSize s.stack)
          (optionMap₂ max (optionMap₂ (· + ·) (sptLookup dest s.stackSize) (some 0))
            (maxDepth s.stackSize (callGraph funs dest [dest] (sptSize funs) body)))))) := by
    intro hrc
    have h := maxDepthCallGraph body _ rc t funs dest a ⟨hcv,
      by show sptSubspt funs (pushEnv envs none (decClock s)).code; rw [hcode1]; exact hcode,
      hl, by
        show sptLookup dest s.stackSize = sptLookup dest (pushEnv envs none (decClock s)).stackSize
        rw [hss1]; rfl, hrc⟩
    rw [hcMax, hcStack, show (WordSemStateFiniteExact.callEnv args1 (sptLookup dest s.stackSize)
      (pushEnv envs none (decClock s))).stackSize = s.stackSize from hss1] at h
    simp only [fullCallGraph, hl, maxDepth] at h
    exact call_some_bound _ _ _ _ _ _ h
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · dsimp only at hev
    by_cases hvalid : x ≠ WordLocW.loc n3 n4 ∨ ys.length ≠ n1.length
    · simp only [hvalid, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    simp only [hvalid, if_false] at hev
    rcases hp : popEnv t with _ | p
    · simp only [hp, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    simp only [hp] at hev
    by_cases hdu : sptDomainEqUnion p.locals envs.1 envs.2
    · simp only [hdu, if_true] at hev
      have hskip := (evaluate_def_rebound (width := width) (C := C) (F := F)).1
        (WordSemStateFiniteExact.setVars n1 ys p)
      rw [hskip, Prod.mk.injEq] at hev
      obtain ⟨-, rfl⟩ := hev
      have pc := popEnvConst t p hp
      have e1 : (WordSemStateFiniteExact.setVars n1 ys p).stackMax = t.stackMax :=
        pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [e1]
      exact hcallee (by simp)
    · simp only [hdu, if_false, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev
    obtain ⟨-, rfl⟩ := hev
    exact hcallee (by simp)
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  all_goals
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    first | exact absurd rfl herr | exact hcallee (by simp)

end Flapjack.Compiler.Backend.WordDepthProof
