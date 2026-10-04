import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallRetArith
import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.CallTail

/-!
# `max_depth_call_graph_lemma`: returning part of the `Call` case

`ret = SOME (rn, names, retH, l1, l2)`. As in HOL: the callee runs in a pushed
frame and is bounded by its induction hypothesis with `delete d funs`, `d`,
`[d]`; a normal return pops the frame (restoring `locals_size` and the stack
size, by `evaluate_stack_swap`) and continues with the return program's
hypothesis; an exception caught by the handler continues likewise from the
`LASTN` handler frame.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact WordSemStackEq

theorem subspt_delete {α : Type} (d : Nat) (f : Spt α) : sptSubspt (sptDelete d f) f := by
  rw [sptSubsptLookup]
  intro k v hk
  rw [sptLookup_sptDelete] at hk
  split at hk
  · cases hk
  · exact hk

/-- The returning-`Call` callee hypothesis of `evaluate_ind` at a concrete
return descriptor. -/
abbrev RetCalleeIH {width : Nat} [NeZero width] {C F : Type}
    (rn : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ xs v3 args1 v10 prog ss v1 n v6 names' v9 retHandler v11 l1' l2' envs,
    WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
    wordSemFindCode dest (wordSemAddRetLoc (some (rn, names, retH, l1, l2)) xs) s.code s.stackSize =
      some v3 ∧
    v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ some (rn, names, retH, l1, l2) = some v1 ∧
    v1 = (n, v6) ∧ v6 = (names', v9) ∧
    v9 = (retHandler, v11) ∧ v11 = (l1', l2') ∧ ¬ (sptDomainEmpty names'.1 ∨ ¬ n.Nodup) ∧
    wordSemCutEnvs names' s.locals = some envs ∧ s.clock ≠ 0 →
    depthPost prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))

/-- The returning-`Call` return-continuation hypothesis of `evaluate_ind`. -/
abbrev RetReturnIH {width : Nat} [NeZero width] {C F : Type}
    (rn : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ xs v3 args1 v10 prog ss v1 n v6 names' v9 retHandler v11 l1' l2' envs v5 s2 v8 x ys s1,
    WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
    wordSemFindCode dest (wordSemAddRetLoc (some (rn, names, retH, l1, l2)) xs) s.code s.stackSize =
      some v3 ∧
    v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ some (rn, names, retH, l1, l2) = some v1 ∧
    v1 = (n, v6) ∧ v6 = (names', v9) ∧
    v9 = (retHandler, v11) ∧ v11 = (l1', l2') ∧ ¬ (sptDomainEmpty names'.1 ∨ ¬ n.Nodup) ∧
    wordSemCutEnvs names' s.locals = some envs ∧ s.clock ≠ 0 ∧
    evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (v5, s2) ∧
    v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1' l2' ∨ ys.length ≠ n.length) ∧
    popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
    depthPost retHandler (WordSemStateFiniteExact.setVars n ys s1)

/-- Returning `Call` without an exception handler (Flapjack infrastructure; the
tagged `Call` case assembles it). -/
theorem depthPost_call_ret_none {width : Nat} [NeZero width] {C F : Type}
    (rn : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact width C F)
    (hreturn : RetReturnIH rn names retH l1 l2 dest args none s)
    (hcallee : RetCalleeIH rn names retH l1 l2 dest args none s) :
    depthPost (.call (some (rn, names, retH, l1, l2)) dest args none) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases dest with _ | d
  · exact post_of_graph_none (by simp [callGraph, maxDepth])
  rcases hfl : sptLookup d funs with _ | ⟨a', body⟩
  · exact post_of_graph_none (by rw [callGraph_call_lookup_none (by simp) hfl]; rfl)
  rw [callGraph_call_ret hfl]
  simp only [maxDepth, maxDepth_mkBranch]
  -- a `NONE` frame size or callee depth makes the bound `NONE`
  by_cases hLn : sptLookup n s.stackSize = none
  · exact post_of_graph_none (by rw [hLn]; rfl)
  by_cases hLd : sptLookup d s.stackSize = none
  · exact post_of_graph_none (by rw [hLd]; cases sptLookup n s.stackSize <;> rfl)
  by_cases hX : maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body) = none
  · exact post_of_graph_none (by
      rw [hX]; cases sptLookup n s.stackSize <;> cases sptLookup d s.stackSize <;> rfl)
  have hy := subspt_lookup_some hsub hfl
  have hyc := subspt_lookup_some hcode hy
  revert herr
  rw [ht]
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · intro herr; exact absurd rfl herr
  have hbad : ¬ wordSemBadDestArgs (some d) args = true := by simp [wordSemBadDestArgs]
  simp only [hbad, Bool.false_eq_true, if_false]
  rcases hf : wordSemFindCode (some d) (wordSemAddRetLoc (some (rn, names, retH, l1, l2)) xs)
      s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · intro herr; exact absurd rfl herr
  obtain ⟨⟨a, hcd⟩, hss, hargs⟩ := findCode_some_dest hf
  rw [hcd] at hyc
  cases hyc
  subst hss
  dsimp only
  by_cases hnames : sptDomainEmpty names.1 ∨ ¬ rn.Nodup
  · simp only [hnames, if_true]; intro herr; exact absurd rfl herr
  simp only [hnames, if_false]
  rcases he : wordSemCutEnvs names s.locals with _ | envs
  · intro herr; exact absurd rfl herr
  dsimp only
  -- the pushed frame and the callee's bound
  have hLnS : s.localsSize = sptLookup n s.stackSize := hloc
  obtain ⟨l0, l, hst0, hmax0, -, -, -, -⟩ := pushEnv_facts envs none s
  have hc0 : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none s)).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax (wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack)))
        (wordSemOptionAdd (wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack))
          (sptLookup d s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs none s).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs none s).stack) (sptLookup d s.stackSize)) = _
    rw [hmax0, hst0, stackSize_cons]
    simp [wordSemStackSizeFrame, hLnS]
  by_cases hz : s.clock = 0
  · simp only [hz, ↓reduceIte]
    intro _
    refine ⟨?_, fun _ => ⟨rfl, fun h => by simp at h⟩⟩
    show optionLe (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none s)).stackMax _
    rw [hc0]
    exact optionLe_trans _ _ _ ⟨(optionLe_X_MAX_X _ _).2, retN_callee _ _ _ _ _ _ _⟩
  simp only [hz, ↓reduceIte]
  -- the callee state
  obtain ⟨l0', l', hst1, hmax1, hss1, -, hcode1, -⟩ := pushEnv_facts envs none (decClock s)
  have hcs : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))).stack = .stackFrame s.localsSize l0' l' none :: s.stack := hst1
  have hcSS : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))).stackSize = s.stackSize := hss1
  have hcCode : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))).code = s.code := hcode1
  have hcStack : wordSemStackSize (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))).stack =
      wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack) := by
    rw [hcs, stackSize_cons]; simp [wordSemStackSizeFrame, hLnS]
  have hcMax : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax (wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack)))
        (wordSemOptionAdd (wordSemOptionAdd (sptLookup n s.stackSize) (wordSemStackSize s.stack))
          (sptLookup d s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs none (decClock s)).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs none (decClock s)).stack) (sptLookup d s.stackSize)) = _
    rw [hmax1, hst1, stackSize_cons]
    simp [wordSemStackSizeFrame, hLnS, decClock]
  rcases hcv : evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s))) with ⟨rc, t⟩
  intro herr
  have herrc : (evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs none (decClock s)))).1 ≠ some .error := by
    rw [hcv]; rintro rfl; simp at herr
  have IH3 := hcallee xs (args1, body, sptLookup d s.stackSize) args1 (body, sptLookup d s.stackSize)
    body (sptLookup d s.stackSize) (rn, names, retH, l1, l2) rn (names, retH, l1, l2) names
    (retH, l1, l2) retH (l1, l2) l1 l2 envs
    ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz⟩
    (sptDelete d funs) d [d] funs2
    ⟨sptSubsptTrans _ _ _ ⟨subspt_delete d funs, hsub⟩, by rw [hcCode]; exact hcode,
      by rw [hcSS]; rfl, herrc, List.mem_singleton_self _, by simp,
      by intro x hx; rw [List.mem_singleton] at hx; subst hx; simp [hy]⟩
  rw [hcv] at IH3
  dsimp only at IH3
  rw [hcMax, hcStack, hcSS] at IH3
  simp only [maxDepthGraphs, hy] at IH3
  have hG3 : optionMap₂ max (sptLookup d s.stackSize)
      (optionMap₂ max (maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body))
        (some 0)) ≠ none := by
    rcases e1 : sptLookup d s.stackSize with _ | _
    · exact absurd e1 hLd
    rcases e2 : maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body) with _ | _
    · exact absurd e2 hX
    simp [optionMap₂]
  obtain ⟨htSS, -⟩ := IH3.2 ⟨hG3, hX⟩
  clear ht hc0 hmax0 hst0 hmax1 hst1
  have hcb := optionLe_trans _ _ _ ⟨IH3.1, retN_callee _ _ _ _
    (maxDepthGraphs s.stackSize ns ns funs funs2) _
    (maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) retH))⟩
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · simp at herr
  · -- normal return: pop the frame and continue with the return program
    dsimp only at herr ⊢
    by_cases hvalid : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ rn.length
    · simp only [hvalid, if_true] at herr; exact absurd rfl herr
    simp only [hvalid, if_false] at herr ⊢
    rcases hp : popEnv t with _ | p
    · simp only [hp] at herr; exact absurd rfl herr
    simp only [hp] at herr ⊢
    by_cases hdu : sptDomainEqUnion p.locals envs.1 envs.2
    · simp only [hdu, if_true] at herr ⊢
      have hsw := evaluateStackSwap body (WordSemStateFiniteExact.callEnv args1
        (sptLookup d s.stackSize) (pushEnv envs none (decClock s)))
      unfold stackSwapPost at hsw
      rw [hcv] at hsw
      rw [hcs] at hsw
      obtain ⟨hpl, hpS⟩ := pop_after_keyEq _ _ _ _ _ t p hsw.1 hp
      have pc := popEnvConst t p hp
      have hgrow := evaluate_code_only_grows body _ _ t hcv
      rw [hcCode] at hgrow
      have IH1 := hreturn xs (args1, body, sptLookup d s.stackSize) args1
        (body, sptLookup d s.stackSize) body (sptLookup d s.stackSize) (rn, names, retH, l1, l2) rn
        (names, retH, l1, l2) names (retH, l1, l2) retH (l1, l2) l1 l2 envs
        (some (.result x ys)) t (.result x ys) x ys p
        ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz, hcv, rfl, rfl, hvalid, hp,
          hdu⟩
        funs n ns funs2
        ⟨hsub, by
          show sptSubspt funs2 p.code
          rw [pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          exact sptSubsptTrans _ _ _ ⟨hcode, hgrow⟩,
         by
          show p.localsSize = sptLookup n p.stackSize
          rw [hpl, pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, htSS]; exact hloc,
         herr, hmem, hnd, hdom⟩
      have e1 : (WordSemStateFiniteExact.setVars rn ys p).stackMax = t.stackMax :=
        pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have e2 : wordSemStackSize (WordSemStateFiniteExact.setVars rn ys p).stack =
          wordSemStackSize s.stack := hpS
      have e3 : (WordSemStateFiniteExact.setVars rn ys p).stackSize = s.stackSize := by
        show p.stackSize = s.stackSize
        rw [pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, htSS]
      have e4 : (WordSemStateFiniteExact.setVars rn ys p).localsSize = s.localsSize := hpl
      rw [e1, e2, e3, e4] at IH1
      refine ⟨optionLe_trans _ _ _ ⟨IH1.1, optionLe_trans _ _ _
        ⟨optionLe_max_mono IH3.1 (optionLe_refl _), retN_return _ _ _ _ _ _ _⟩⟩, fun hne => ?_⟩
      have hR : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) retH) ≠ none := by
        intro h0; apply hne.2; rw [h0, optionMap2_none_right, optionMap2_none_right]
      exact IH1.2 ⟨hne.1, hR⟩
    · simp only [hdu, if_false] at herr; exact absurd rfl herr
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · simp at herr
  · simp at herr
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · simp at herr

/-- The returning-`Call` exception-handler hypothesis of `evaluate_ind`. -/
abbrev RetExceptionIH {width : Nat} [NeZero width] {C F : Type}
    (rn : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ xs v3 args1 v10 prog ss v1 n v6 names' v9 retHandler v11 l1' l2' envs v5 s2 v8 x' y v n' v2
    h v4 l1'' l2'',
    WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
    wordSemFindCode dest (wordSemAddRetLoc (some (rn, names, retH, l1, l2)) xs) s.code s.stackSize =
      some v3 ∧
    v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ some (rn, names, retH, l1, l2) = some v1 ∧
    v1 = (n, v6) ∧ v6 = (names', v9) ∧
    v9 = (retHandler, v11) ∧ v11 = (l1', l2') ∧ ¬ (sptDomainEmpty names'.1 ∨ ¬ n.Nodup) ∧
    wordSemCutEnvs names' s.locals = some envs ∧ s.clock ≠ 0 ∧
    evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (v5, s2) ∧
    v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
    v4 = (l1'', l2'') ∧ x' = .loc l1'' l2'' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
    depthPost h (WordSemStateFiniteExact.setVar n' y s2)

/-- Returning `Call` with an exception handler (Flapjack infrastructure; the
tagged `Call` case assembles it). -/
theorem depthPost_call_ret_some {width : Nat} [NeZero width] {C F : Type}
    (rn : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (hn : Nat) (hprog : WordLangProgHOL (BitVec width)) (hl1 hl2 : Nat)
    (s : WordSemStateFiniteExact width C F)
    (hreturn : RetReturnIH rn names retH l1 l2 dest args (some (hn, hprog, hl1, hl2)) s)
    (hexception : RetExceptionIH rn names retH l1 l2 dest args (some (hn, hprog, hl1, hl2)) s)
    (hcallee : RetCalleeIH rn names retH l1 l2 dest args (some (hn, hprog, hl1, hl2)) s) :
    depthPost (.call (some (rn, names, retH, l1, l2)) dest args (some (hn, hprog, hl1, hl2))) s := by
  intro funs n ns funs2 ⟨hsub, hcode, hloc, herr, hmem, hnd, hdom⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases dest with _ | d
  · exact post_of_graph_none (by simp [callGraph, maxDepth])
  rcases hfl : sptLookup d funs with _ | ⟨a', body⟩
  · exact post_of_graph_none (by rw [callGraph_call_lookup_none (by simp) hfl]; rfl)
  rw [callGraph_call_ret hfl]
  simp only [maxDepth, maxDepth_mkBranch]
  by_cases hLn : sptLookup n s.stackSize = none
  · exact post_of_graph_none (by rw [hLn]; rfl)
  by_cases hLd : sptLookup d s.stackSize = none
  · exact post_of_graph_none (by rw [hLd]; cases sptLookup n s.stackSize <;> rfl)
  by_cases hX : maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body) = none
  · exact post_of_graph_none (by
      rw [hX]; cases sptLookup n s.stackSize <;> cases sptLookup d s.stackSize <;> rfl)
  have hy := subspt_lookup_some hsub hfl
  have hyc := subspt_lookup_some hcode hy
  revert herr
  rw [ht]
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · intro herr; exact absurd rfl herr
  have hbad : ¬ wordSemBadDestArgs (some d) args = true := by simp [wordSemBadDestArgs]
  simp only [hbad, Bool.false_eq_true, if_false]
  rcases hf : wordSemFindCode (some d) (wordSemAddRetLoc (some (rn, names, retH, l1, l2)) xs)
      s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · intro herr; exact absurd rfl herr
  obtain ⟨⟨a, hcd⟩, hss, hargs⟩ := findCode_some_dest hf
  rw [hcd] at hyc
  cases hyc
  subst hss
  dsimp only
  by_cases hnames : sptDomainEmpty names.1 ∨ ¬ rn.Nodup
  · simp only [hnames, if_true]; intro herr; exact absurd rfl herr
  simp only [hnames, if_false]
  rcases he : wordSemCutEnvs names s.locals with _ | envs
  · intro herr; exact absurd rfl herr
  dsimp only
  have hLnS : s.localsSize = sptLookup n s.stackSize := hloc
  obtain ⟨l0, l, hst0, hmax0, -, -, -, -⟩ := pushEnv_facts envs (some (hn, hprog, hl1, hl2)) s
  have hc0 : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) s)).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax
          (wordSemOptionAdd ((sptLookup n s.stackSize).map (3 + ·)) (wordSemStackSize s.stack)))
        (wordSemOptionAdd
          (wordSemOptionAdd ((sptLookup n s.stackSize).map (3 + ·)) (wordSemStackSize s.stack))
          (sptLookup d s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs (some (hn, hprog, hl1, hl2)) s).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs (some (hn, hprog, hl1, hl2)) s).stack)
        (sptLookup d s.stackSize)) = _
    rw [hmax0, hst0, stackSize_cons]
    simp [wordSemStackSizeFrame, hLnS]
  by_cases hz : s.clock = 0
  · simp only [hz, ↓reduceIte]
    intro _
    refine ⟨?_, fun _ => ⟨rfl, fun h => by simp at h⟩⟩
    show optionLe (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) s)).stackMax _
    rw [hc0]
    exact optionLe_trans _ _ _ ⟨(optionLe_X_MAX_X _ _).2, retS_callee _ _ _ _ _ _ _ _⟩
  simp only [hz, ↓reduceIte]
  obtain ⟨l0', l', hst1, hmax1, hss1, -, hcode1, hhd1⟩ :=
    pushEnv_facts envs (some (hn, hprog, hl1, hl2)) (decClock s)
  have hcs : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).stack =
      .stackFrame s.localsSize l0' l' (some (s.handler, hl1, hl2)) :: s.stack := hst1
  have hch : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).handler = s.stack.length :=
    hhd1 rfl
  have hcSS : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).stackSize = s.stackSize := hss1
  have hcCode : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).code = s.code := hcode1
  have hcStack : wordSemStackSize (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).stack =
      wordSemOptionAdd ((sptLookup n s.stackSize).map (3 + ·)) (wordSemStackSize s.stack) := by
    rw [hcs, stackSize_cons]; simp [wordSemStackSizeFrame, hLnS]
  have hcMax : (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))).stackMax =
      wordSemOptionMax
        (wordSemOptionMax s.stackMax
          (wordSemOptionAdd ((sptLookup n s.stackSize).map (3 + ·)) (wordSemStackSize s.stack)))
        (wordSemOptionAdd
          (wordSemOptionAdd ((sptLookup n s.stackSize).map (3 + ·)) (wordSemStackSize s.stack))
          (sptLookup d s.stackSize)) := by
    show wordSemOptionMax (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s)).stackMax
      (wordSemOptionAdd (wordSemStackSize (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s)).stack)
        (sptLookup d s.stackSize)) = _
    rw [hmax1, hst1, stackSize_cons]
    simp [wordSemStackSizeFrame, hLnS, decClock]
  rcases hcv : evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s))) with ⟨rc, t⟩
  intro herr
  have herrc : (evaluate body (WordSemStateFiniteExact.callEnv args1 (sptLookup d s.stackSize)
      (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s)))).1 ≠ some .error := by
    rw [hcv]; rintro rfl; simp at herr
  have IH3 := hcallee xs (args1, body, sptLookup d s.stackSize) args1 (body, sptLookup d s.stackSize)
    body (sptLookup d s.stackSize) (rn, names, retH, l1, l2) rn (names, retH, l1, l2) names
    (retH, l1, l2) retH (l1, l2) l1 l2 envs
    ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz⟩
    (sptDelete d funs) d [d] funs2
    ⟨sptSubsptTrans _ _ _ ⟨subspt_delete d funs, hsub⟩, by rw [hcCode]; exact hcode,
      by rw [hcSS]; rfl, herrc, List.mem_singleton_self _, by simp,
      by intro x hx; rw [List.mem_singleton] at hx; subst hx; simp [hy]⟩
  rw [hcv] at IH3
  dsimp only at IH3
  rw [hcMax, hcStack, hcSS] at IH3
  simp only [maxDepthGraphs, hy] at IH3
  have hG3 : optionMap₂ max (sptLookup d s.stackSize)
      (optionMap₂ max (maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body))
        (some 0)) ≠ none := by
    rcases e1 : sptLookup d s.stackSize with _ | _
    · exact absurd e1 hLd
    rcases e2 : maxDepth s.stackSize (callGraph (sptDelete d funs) d [d] (sptSize funs2) body) with _ | _
    · exact absurd e2 hX
    simp [optionMap₂]
  obtain ⟨htSS, -⟩ := IH3.2 ⟨hG3, hX⟩
  clear ht hc0 hmax0 hst0 hmax1 hst1
  have hcb := optionLe_trans _ _ _ ⟨IH3.1, retS_callee _ _ _ _
    (maxDepthGraphs s.stackSize ns ns funs funs2) _
    (maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) retH))
    (maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) hprog))⟩
  have hgrow := evaluate_code_only_grows body _ _ t hcv
  rw [hcCode] at hgrow
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · simp at herr
  · -- normal return: pop the frame and continue with the return program
    dsimp only at herr ⊢
    by_cases hvalid : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ rn.length
    · simp only [hvalid, if_true] at herr; exact absurd rfl herr
    simp only [hvalid, if_false] at herr ⊢
    rcases hp : popEnv t with _ | p
    · simp only [hp] at herr; exact absurd rfl herr
    simp only [hp] at herr ⊢
    by_cases hdu : sptDomainEqUnion p.locals envs.1 envs.2
    · simp only [hdu, if_true] at herr ⊢
      have hsw := evaluateStackSwap body (WordSemStateFiniteExact.callEnv args1
        (sptLookup d s.stackSize) (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s)))
      unfold stackSwapPost at hsw
      rw [hcv] at hsw
      rw [hcs] at hsw
      obtain ⟨hpl, hpS⟩ := pop_after_keyEq _ _ _ _ _ t p hsw.1 hp
      have pc := popEnvConst t p hp
      have IH1 := hreturn xs (args1, body, sptLookup d s.stackSize) args1
        (body, sptLookup d s.stackSize) body (sptLookup d s.stackSize) (rn, names, retH, l1, l2) rn
        (names, retH, l1, l2) names (retH, l1, l2) retH (l1, l2) l1 l2 envs
        (some (.result x ys)) t (.result x ys) x ys p
        ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz, hcv, rfl, rfl, hvalid, hp,
          hdu⟩
        funs n ns funs2
        ⟨hsub, by
          show sptSubspt funs2 p.code
          rw [pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
          exact sptSubsptTrans _ _ _ ⟨hcode, hgrow⟩,
         by
          show p.localsSize = sptLookup n p.stackSize
          rw [hpl, pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, htSS]; exact hloc,
         herr, hmem, hnd, hdom⟩
      have e1 : (WordSemStateFiniteExact.setVars rn ys p).stackMax = t.stackMax :=
        pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have e2 : wordSemStackSize (WordSemStateFiniteExact.setVars rn ys p).stack =
          wordSemStackSize s.stack := hpS
      have e3 : (WordSemStateFiniteExact.setVars rn ys p).stackSize = s.stackSize := by
        show p.stackSize = s.stackSize
        rw [pc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, htSS]
      have e4 : (WordSemStateFiniteExact.setVars rn ys p).localsSize = s.localsSize := hpl
      rw [e1, e2, e3, e4] at IH1
      refine ⟨optionLe_trans _ _ _ ⟨IH1.1, optionLe_trans _ _ _
        ⟨optionLe_max_mono IH3.1 (optionLe_refl _), retS_return _ _ _ _ _ _ _ _⟩⟩, fun hne => ?_⟩
      have hR : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) retH) ≠ none := by
        intro h0; apply hne.2
        rw [h0, optionMap2_none_right, optionMap2_none_right, optionMap2_none_right]
      exact IH1.2 ⟨hne.1, hR⟩
    · simp only [hdu, if_false] at herr; exact absurd rfl herr
  · -- exception caught by the handler
    dsimp only at herr ⊢
    by_cases hxl : x ≠ WordLocW.loc hl1 hl2
    · rw [if_pos hxl] at herr; exact absurd rfl herr
    rw [if_neg hxl] at herr ⊢
    by_cases hdu : sptDomainEqUnion t.locals envs.1 envs.2
    · simp only [hdu, if_true] at herr ⊢
      have hsw := evaluateStackSwap body (WordSemStateFiniteExact.callEnv args1
        (sptLookup d s.stackSize) (pushEnv envs (some (hn, hprog, hl1, hl2)) (decClock s)))
      unfold stackSwapPost at hsw
      rw [hcv] at hsw
      obtain ⟨-, e0, e, n0, ls, m, lss, hlast, hm, -, hkey, -⟩ := hsw
      rw [hch, hcs, wordSemLastN_length_succ] at hlast
      simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq] at hlast
      obtain ⟨⟨hms, -, -, -⟩, hls⟩ := hlast
      subst hls
      have htl : t.localsSize = s.localsSize := by rw [← hm, hms]
      have htS : wordSemStackSize t.stack = wordSemStackSize s.stack :=
        (sKeyEqStackSize _ _ hkey)
      have IH2 := hexception xs (args1, body, sptLookup d s.stackSize) args1
        (body, sptLookup d s.stackSize) body (sptLookup d s.stackSize) (rn, names, retH, l1, l2) rn
        (names, retH, l1, l2) names (retH, l1, l2) retH (l1, l2) l1 l2 envs
        (some (.exception x y)) t (.exception x y) x y (hn, hprog, hl1, hl2) hn (hprog, hl1, hl2)
        hprog (hl1, hl2) hl1 hl2
        ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz, hcv, rfl, rfl, rfl, rfl,
          rfl, rfl, not_not.mp hxl, hdu⟩
        funs n ns funs2
        ⟨hsub, sptSubsptTrans _ _ _ ⟨hcode, hgrow⟩,
         by
          show t.localsSize = sptLookup n t.stackSize
          rw [htl, htSS]; exact hloc,
         herr, hmem, hnd, hdom⟩
      have e1 : (WordSemStateFiniteExact.setVar hn y t).stackMax = t.stackMax := rfl
      have e2 : wordSemStackSize (WordSemStateFiniteExact.setVar hn y t).stack =
          wordSemStackSize s.stack := htS
      have e3 : (WordSemStateFiniteExact.setVar hn y t).stackSize = s.stackSize := htSS
      have e4 : (WordSemStateFiniteExact.setVar hn y t).localsSize = s.localsSize := htl
      rw [e1, e2, e3, e4] at IH2
      refine ⟨optionLe_trans _ _ _ ⟨IH2.1, optionLe_trans _ _ _
        ⟨optionLe_max_mono IH3.1 (optionLe_refl _), retS_handler _ _ _ _ _ _ _ _⟩⟩, fun hne => ?_⟩
      have hH : maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) hprog) ≠ none := by
        intro h0; apply hne.2
        rw [h0]
        rcases maxDepth s.stackSize (callGraph funs n ns (sptSize funs2) retH) <;>
          simp [optionMap₂]
      exact IH2.2 ⟨hne.1, hH⟩
    · simp only [hdu, if_false] at herr; exact absurd rfl herr
  · simp at herr
  · simp at herr
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · dsimp only
    exact ⟨hcb, fun _ => ⟨htSS, fun h => by simp at h⟩⟩
  · simp at herr

end Flapjack.Compiler.Backend.WordDepthProof
