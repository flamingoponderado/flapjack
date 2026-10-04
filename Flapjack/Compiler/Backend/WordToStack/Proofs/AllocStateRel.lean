import Flapjack.Compiler.Backend.WordToStack.Proofs.GcSimulation
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Misc.Sptree.Wf

/-!
# Word-to-Stack allocation simulation: `alloc_IMP_alloc`, `alloc_IMP_alloc2`

WordSem `alloc` is simulated by StackSem `alloc`
(`word_to_stackProofScript.sml:2131-2380`), with live variables either spilled
into a frame by `wLive` (`alloc_IMP_alloc`) or, at frame size `0`, absent
(`alloc_IMP_alloc2`).
-/

namespace Flapjack.WordToStackProofs.AllocStateRel
open Flapjack.StackSem Flapjack.Compiler.Encoders.Asm Flapjack.WordSemStateFiniteExact
  Flapjack.WordSemStackEq

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

/-- Canonical source-state codec re-export for the WordSem carrier
(`fmap_as_finite_support` on `word_gc_empty_frame`); no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Inhabitation of the source frame carrier for total HOL `EL`, as in `stackRelAux`. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- WordSem and StackSem `has_space` agree on stores that differ only at
`Handler`. Flapjack helper; no separate HOL original. -/
theorem hasSpace_eraseHandler {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (h : s.store = store.eraseEq .handler) (w : WordLocW width) :
    hasSpace w s = StackSemAllocation.hasSpace w store := by
  simp only [hasSpace, StackSemAllocation.hasSpace, getStore, h, HolFiniteMapExact.eraseEq,
    FDOMSUB_HOL, reduceCtorEq, if_false]
  generalize store.lookup .nextFree = a
  generalize store.lookup .triggerGC = b
  rcases w with w | ⟨_, _⟩ <;> rcases a with _ | (a | ⟨_, _⟩) <;>
    rcases b with _ | (b | ⟨_, _⟩) <;> rfl

/-- A successful `cut_envs` returns the two intersections. Flapjack helper; no
separate HOL original. -/
theorem cutEnvs_eq {β : Type} {names : WordLangCutsetsHOL} {env : Spt β}
    {envs : Spt β × Spt β} (h : wordSemCutEnvs names env = some envs) :
    envs.1 = sptInter env names.1 ∧ envs.2 = sptInter env names.2 := by
  unfold wordSemCutEnvs wordSemCutNames at h
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 env <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 env <;>
    simp only [h1, h2, if_true, if_false, Option.some.injEq, reduceCtorEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- Exact HOL `alloc_IMP_alloc` (`word_to_stackProofScript.sml:2131-2318`). HOL's
free `c`, `names`, `k`, `f`, `f'`, `lens` and `envs` are explicit; `x ∈ domain t`
is `sptDomain t x` and `EVEN x` is `x % 2 = 0`. The pushed-frame state is HOL's
`push_env envs NONE s with <|locals := LN; locals_size := SOME 0|>`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allocImpAlloc {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f f' : Nat) (c : BitVec width) (names : WordLangCutsetsHOL)
    (s s1 : WordSemStateFiniteExact width (Nat × C) F) (res : Option (WordSemResult width))
    (t5 : StackSemStateFiniteExact width C F) (lens : List Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) :
    alloc c names s = (res, s1) ∧
      (∀ x, sptDomain names.1 x → x % 2 = 0 ∧ k ≤ x / 2) ∧
      (∀ x, sptDomain names.2 x → x % 2 = 0 ∧ k ≤ x / 2) ∧
      1 ≤ f ∧ stateRel ac k f f' s t5 lens 0 ∧
      stateRel ac k 0 0 { pushEnv envs none s with locals := .ln, localsSize := some 0 } t5
        (f' :: lens) 0 ∧
      wordSemCutEnvs names s.locals = some envs ∧ res ≠ some .error →
    ∃ t1 res1, StackSemAllocation.alloc c t5 = (res1, t1) ∧
      if res = none then
        res1 = none ∧ stateRel ac k f f' s1 t1 lens 0 ∧ t1.stack.length = t5.stack.length ∧
          t1.stackSpace = t5.stackSpace
      else
        res = some .notEnoughSpace ∧ res1 = some (.halt (.word 1)) ∧ s1.clock = t1.clock ∧
          s1.ffi = t1.ffi := by
  rintro ⟨halloc, hfst, hsnd, hf1, hrel, hpush, hcut, hnerr⟩
  have hres : (alloc c names s).1 ≠ some .error := by rw [halloc]; exact hnerr
  rw [AllocSimulation.allocAlt c names s hres, hcut] at halloc
  simp only at halloc
  have hset := AllocSimulation.stateRelSetStore0 ac k _ t5 (f' :: lens) 0 (.word c) hpush
  rcases hgc : WordSemStateFiniteExact.gc (setStore .allocSize (.word c)
      { pushEnv envs none s with locals := .ln, localsSize := some 0 }) with _ | s2
  · simp only [hgc, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hgc] at halloc
  obtain ⟨t2, ht2gc, hR2, ht2len, ht2sp⟩ :=
    GcSimulation.gcStateRel ac k _ s2 _ (f' :: lens) ⟨hgc, hset⟩
  have hkey := WordSemStackEq.gcSKeyEq _ _ hgc
  obtain ⟨n, l, ls, opt, hs2stack, -⟩ := WordSemStackEq.pushEnvPopEnvSKeyEq envs none s s2
    (by simpa [setStore] using hkey)
  simp only [setStore, pushEnv, hs2stack, sKeyEq] at hkey
  rcases opt with _ | ⟨h1, l1, l2⟩
  swap
  · simp [sFrameKeyEq] at hkey
  simp only [sFrameKeyEq] at hkey
  obtain ⟨-, hlkeys, -, hn⟩ := hkey
  subst hn
  have hpop : s2.popEnv = some { s2 with
      locals := sptUnion (sptFromAList l) (sptFromAList (sptToAList envs.1))
      stack := ls
      localsSize := s.localsSize } := by
    unfold WordSemStateFiniteExact.popEnv
    rw [hs2stack]
  rw [hpop] at halloc
  simp only at halloc
  have hclaim : stateRel ac k f f' { s2 with
      locals := sptUnion (sptFromAList l) (sptFromAList (sptToAList envs.1))
      stack := ls
      localsSize := s.localsSize } t2 lens 0 := by
    obtain ⟨he1, he2⟩ := cutEnvs_eq hcut
    have hcut1 : ∀ n v, sptLookup n envs.1 = some v → sptDomain names.1 n := by
      intro n v hn
      rw [he1, sptLookup_sptInterCases] at hn
      unfold sptDomain
      cases h : sptLookup n names.1 <;> simp_all
    have hcut2 : ∀ n v, sptLookup n envs.2 = some v → sptDomain names.2 n := by
      intro n v hn
      rw [he2, sptLookup_sptInterCases] at hn
      unfold sptDomain
      cases h : sptLookup n names.2 <;> simp_all
    have hR2' := hR2
    unfold stateRel at hR2'
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
      g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, -, g34, -, -,
      g37, g38, -⟩ := hR2'
    have hrel' := hrel
    unfold stateRel at hrel'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, r35, -, -, -, -⟩ := hrel'
    have hff : f = f' + 1 := by
      by_cases h0 : f' = 0
      · rw [if_pos h0] at r35; omega
      · rw [if_neg h0] at r35; exact r35
    simp only [Nat.add_zero, List.drop_zero] at g38
    rw [hs2stack] at g38 g37
    obtain ⟨gsorted, astack, gabs, gH, gaux⟩ := g38
    generalize hD : t2.stack.drop t2.stackSpace = D at gabs
    rcases D with _ | ⟨w, rest⟩
    · rw [absStack.eq_def] at gabs; simp at gabs
    rw [absStack.eq_def] at gabs
    simp only at gabs
    rcases hb : fullReadBitmap t2.bitmaps w with _ | bits
    · simp [hb] at gabs
    simp only [hb] at gabs
    split at gabs
    · simp at gabs
    split at gabs
    · simp at gabs
    rename_i hlen0 hrestlen
    rcases hys : absStack t2.bitmaps ls (rest.drop f') lens with _ | ys
    · simp [hys] at gabs
    simp only [hys, Option.some.injEq] at gabs
    subst gabs
    have hbl : bits.length = f' := by simpa using hlen0
    simp only [stackRelAux] at gaux
    obtain ⟨gA, gB, gC, gaux'⟩ := gaux
    have htakeLen : (rest.take f').length = f' := by simp; omega
    rw [htakeLen] at gC
    have hDlen := congrArg List.length hD
    simp only [List.length_drop, List.length_cons] at hDlen
    unfold stateRel
    refine ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
      g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, ?_, g34, r35,
      sptWfUnion _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩, ?_, ?_⟩
    · show t2.stackSpace + f ≤ t2.stack.length
      omega
    · show stackSizeRel f s.localsSize s2.stackLimit s2.stackMax ls t2.stack t2.stackSpace 0
      obtain ⟨-, glim, gmax⟩ := g37
      have hls : s.localsSize.getD f = f := by rw [hff]; exact gC
      refine ⟨fun _ => hls, glim, ?_⟩
      intro m hm
      obtain ⟨hle, -, size, hsize, hsz⟩ := gmax m hm
      have hcons : wordSemStackSize
          (WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1) l none :: ls) =
          wordSemOptionAdd s.localsSize (wordSemStackSize ls) := rfl
      rw [hcons] at hsize
      rcases hloc : s.localsSize with _ | a
      · rw [hloc] at hsize; simp [wordSemOptionAdd] at hsize
      rcases hrestsz : wordSemStackSize ls with _ | b
      · rw [hloc, hrestsz] at hsize; simp [wordSemOptionAdd] at hsize
      rw [hloc, hrestsz] at hsize
      simp only [wordSemOptionAdd, Option.some.injEq] at hsize
      have ha : a = f := by rw [hloc] at hls; simpa using hls
      refine ⟨by omega, by simp, b, rfl, by omega⟩
    · have hlsLen : ys.length = ls.length := (absStackImpLength _ _ _ _ _ hys).1
      refine ⟨?_, ?_⟩
      · show stackRel k s2.handler ls (t2.store.lookup .handler)
          ((t2.stack.drop (t2.stackSpace + 0)).drop f) t2.stack.length t2.bitmaps lens
        rw [Nat.add_zero, hD, hff, List.drop_succ_cons]
        refine ⟨?_, ys, hys, ?_, gaux'⟩
        · simp only [List.all_cons, Bool.and_eq_true] at gsorted; exact gsorted.2
        · intro hlt hhandler
          have hH := gH (by simp; omega) (by
            simp only [List.length_cons]
            rw [show ls.length + 1 - (s2.handler + 1) = (ls.length - (s2.handler + 1)) + 1 by omega,
              holEl_cons_succ]
            exact hhandler)
          rw [hH]
          simp only [List.length_cons]
          rw [show ys.length + 1 - (s2.handler + 1) = (ys.length - (s2.handler + 1)) + 1 by omega,
            List.drop_succ_cons]
      · intro n v hn
        show n % 2 = 0 ∧ if n / 2 < k then t2.regs.lookup (n / 2) = some v
          else ((t2.stack.drop (t2.stackSpace + 0)).take f)[f - 1 - (n / 2 - k)]? = some v ∧
            n / 2 < k + f'
        rw [Nat.add_zero, hD, hff, List.take_succ_cons]
        simp only at hn
        rw [sptLookup_sptUnion] at hn
        rcases hl : sptLookup n (sptFromAList l) with _ | v'
        · rw [hl] at hn
          rw [sptLookup_sptFromAList_sptToAList] at hn
          obtain ⟨heven, hk⟩ := hfst n (hcut1 n v hn)
          refine ⟨heven, ?_⟩
          rw [if_neg (by omega)]
          have hl0 : (sptToAList envs.1).lookup n = some v := by
            rw [GcSimulation.lookup_eq_sptAListLookup, ← sptLookup_sptFromAList,
              sptLookup_sptFromAList_sptToAList]
            exact hn
          have hlnone : l.lookup n = none := by
            rw [GcSimulation.lookup_eq_sptAListLookup, ← sptLookup_sptFromAList]; exact hl
          obtain ⟨ha, -, hc⟩ := gA n v hl0 hlnone
          rw [hbl] at ha
          simp only [adjustNames] at ha
          rw [GcSimulation.lookup_eq_sptAListLookup,
            aLookupIndexList _ _ _ (by rw [htakeLen]; omega), htakeLen] at hc
          refine ⟨?_, by omega⟩
          rw [show f' + 1 - 1 - (n / 2 - k) = (f' + k - (n / 2 + 1)) + 1 by omega,
            List.getElem?_cons_succ]
          exact hc
        · rw [hl] at hn
          simp only [Option.some.injEq] at hn
          subst hn
          rw [sptLookup_sptFromAList] at hl
          have hmem := sptAListLookup_mem n l v' hl
          have hkey : n ∈ (wordSemEnvToList envs.2 s.permute).1.map Prod.fst := by
            rw [hlkeys]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
          obtain ⟨⟨n0, v0⟩, hmem0, hn0⟩ := List.mem_map.mp hkey
          simp only at hn0
          subst hn0
          rw [wordSemEnvToList_mem_iff, sptToAList_mem_iff_lookup] at hmem0
          obtain ⟨heven, hk⟩ := hsnd n0 (hcut2 n0 v0 hmem0)
          refine ⟨heven, ?_⟩
          rw [if_neg (by omega)]
          have hsel : (adjustNames n0, v') ∈ l.map (fun p => (adjustNames p.1, p.2)) :=
            List.mem_map.mpr ⟨_, hmem, rfl⟩
          have hidx := Compiler.Backend.WordToStack.filterBitmapMem bits _ _ _ gB hsel
          have hlim := memIndexListLim _ _ _ _ hidx
          have hel := memIndexListEl _ _ _ _ hidx
          have hel' := List.getElem?_eq_some_iff.mpr ⟨_, hel⟩
          simp only [adjustNames, htakeLen] at hlim hel'
          refine ⟨?_, by omega⟩
          rw [show f' + 1 - 1 - (n0 / 2 - k) = (f' - (n0 / 2 - k + 1)) + 1 by omega,
            List.getElem?_cons_succ]
          exact hel'
  have hstore : s2.store = t2.store.eraseEq .handler := by
    unfold stateRel at hclaim; exact hclaim.2.2.2.2.2.2.2.2.2.2.2.1
  have hclock : s2.clock = t2.clock := by
    unfold stateRel at hclaim; exact hclaim.1
  have hffi : t2.ffi = s2.ffi := by
    unfold stateRel at hclaim; exact hclaim.2.2.2.1
  have hget : ∀ s' : WordSemStateFiniteExact width (Nat × C) F, s'.store = s2.store →
      getStore .allocSize s' = t2.store.lookup .allocSize := by
    intro s' h'
    simp [getStore, h', hstore, HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
  set s3 : WordSemStateFiniteExact width (Nat × C) F := { s2 with
      locals := sptUnion (sptFromAList l) (sptFromAList (sptToAList envs.1))
      stack := ls
      localsSize := s.localsSize } with hs3
  rw [hget s3 rfl] at halloc
  rcases hw : t2.store.lookup .allocSize with _ | w
  · simp only [hw, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hw] at halloc
  rw [hasSpace_eraseHandler s3 t2.store hstore] at halloc
  rcases hb : StackSemAllocation.hasSpace w t2.store with _ | _ | _
  · simp only [hb, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  · simp only [hb, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    refine ⟨StackSemStateOps.emptyEnv t2, some (.halt (.word 1)),
      by simp only [StackSemAllocation.alloc, ht2gc, hw, hb], ?_⟩
    simp only [reduceCtorEq, if_false, true_and]
    exact ⟨hclock, hffi.symm⟩
  · simp only [hb, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    refine ⟨t2, none, by simp only [StackSemAllocation.alloc, ht2gc, hw, hb], ?_⟩
    simp only [if_true, true_and]
    exact ⟨hclaim, by rw [ht2len]; rfl, by rw [ht2sp]; rfl⟩

/-- Exact HOL `word_gc_empty_frame` (`word_to_stackProofScript.sml:2320-2332`):
collecting under an empty frame without a handler, then popping it, is
collecting without it. HOL's free `n` is explicit. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordGcEmptyFrame {width : Nat} [NeZero width] {C F : Type}
    (s x y : WordSemStateFiniteExact width C F) (n : Option Nat) :
    gc { s with stack := .stackFrame n [] [] none :: s.stack } = some x ∧ popEnv x = some y →
      y.locals = .ln ∧ gc s = some { y with locals := s.locals, localsSize := s.localsSize } := by
  rintro ⟨hgc, hpop⟩
  simp only [gc, wordSemEncStack, List.map_nil, List.nil_append] at hgc ⊢
  rcases hf : s.gcFun (wordSemEncStack s.stack, s.memory, s.mdomain, s.store) with _ | ⟨wl, m, st⟩
  · simp [hf] at hgc
  simp only [hf] at hgc ⊢
  simp only [wordSemDecStack, List.length_nil, Nat.not_lt_zero, if_false, List.drop_zero] at hgc
  rcases hd : wordSemDecStack wl s.stack with _ | st'
  · simp [hd] at hgc
  simp only [hd, Option.some.injEq] at hgc
  subst hgc
  simp only [popEnv, Option.some.injEq] at hpop
  subst hpop
  exact ⟨by simp [sptFromAList, sptUnion], rfl⟩

/-- Exact HOL `inter_eq_empty_2` (`word_to_stackProofScript.sml:2327-2332`). HOL
`domain t = {}` is the empty characteristic predicate. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "inter_eq_empty_2"]
theorem interEqEmpty2 {α β : Type} (s : Spt α) (t : Spt β) :
    sptDomain t = (fun _ => False) → sptInter s t = .ln := by
  intro h
  have hn : ∀ n, sptLookup n t = none := by
    intro n
    have := congrFun h n
    simp only [sptDomain, eq_iff_iff, iff_false, Option.isSome_iff_ne_none, ne_eq,
      Decidable.not_not] at this
    exact this
  clear h
  induction s generalizing t with
  | ln => simp [sptInter]
  | ls v =>
      cases t with
      | ln => simp [sptInter]
      | ls _ => simpa [sptLookup] using hn 0
      | bn _ _ => simp [sptInter]
      | bs _ _ _ => simpa [sptLookup] using hn 0
  | bn a b iha ihb =>
      cases t with
      | ln => simp [sptInter]
      | ls _ => simp [sptInter]
      | bn a' b' =>
          simp only [sptInter]
          rw [iha a' (fun m => by
              have h := hn (2 * m + 2); simp [sptLookup] at h
              rwa [show (2 * m + 1) / 2 = m by omega] at h),
            ihb b' (fun m => by simpa [sptLookup] using hn (2 * m + 1))]
          rfl
      | bs _ _ _ => simpa [sptLookup] using hn 0
  | bs a v b iha ihb =>
      cases t with
      | ln => simp [sptInter]
      | ls _ => simpa [sptLookup] using hn 0
      | bn a' b' =>
          simp only [sptInter]
          rw [iha a' (fun m => by
              have h := hn (2 * m + 2); simp [sptLookup] at h
              rwa [show (2 * m + 1) / 2 = m by omega] at h),
            ihb b' (fun m => by simpa [sptLookup] using hn (2 * m + 1))]
          rfl
      | bs _ _ _ => simpa [sptLookup] using hn 0

theorem gc_stackMax {width : Nat} [NeZero width] {C F : Type}
    {s s' : WordSemStateFiniteExact width C F} (h : gc s = some s') :
    s'.stackMax = s.stackMax ∧ s'.handler = s.handler := by
  simp only [gc] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩

/-- Exact HOL `alloc_IMP_alloc2` (`word_to_stackProofScript.sml:2334-2380`). HOL's
free `c`, `names`, `k` and `lens` are explicit; `domain t = {}` is the empty
characteristic predicate. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allocImpAlloc2 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat) (c : BitVec width) (names : WordLangCutsetsHOL)
    (s s1 : WordSemStateFiniteExact width (Nat × C) F) (res : Option (WordSemResult width))
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) :
    alloc c names s = (res, s1) ∧ stateRel ac k 0 0 s t lens 0 ∧
      sptDomain names.1 = (fun _ => False) ∧ sptDomain names.2 = (fun _ => False) ∧
      res ≠ some .error →
    ∃ t1 res1, StackSemAllocation.alloc c t = (res1, t1) ∧
      if res = none then
        res1 = none ∧ stateRel ac k 0 0 s1 t1 lens 0 ∧ t1.stack.length = t.stack.length ∧
          t1.stackSpace = t.stackSpace
      else
        res = some .notEnoughSpace ∧ res1 = some (.halt (.word 1)) ∧ s1.clock = t1.clock ∧
          s1.ffi = t1.ffi := by
  rintro ⟨halloc, hrel, hd1, hd2, hnerr⟩
  have hres : (alloc c names s).1 ≠ some .error := by rw [halloc]; exact hnerr
  rw [AllocSimulation.allocAlt c names s hres] at halloc
  rcases hcut : wordSemCutEnvs names s.locals with _ | envs
  · simp only [hcut, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hcut] at halloc
  obtain ⟨he1, he2⟩ := cutEnvs_eq hcut
  rw [interEqEmpty2 _ _ hd1] at he1
  rw [interEqEmpty2 _ _ hd2] at he2
  obtain ⟨e1, e2⟩ := envs
  simp only at he1 he2
  subst he1 he2
  have htoal : sptToAList (.ln : Spt (WordLocW width)) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    rintro ⟨a, b⟩ h
    rw [sptToAList_mem_iff_lookup] at h
    simp [sptLookup] at h
  have henv : (wordSemEnvToList (.ln : Spt (WordLocW width)) s.permute).1 = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro e h
    rw [wordSemEnvToList_mem_iff, htoal] at h
    simp at h
  let B' : WordSemStateFiniteExact width (Nat × C) F := { s with
    locals := .ln
    localsSize := some 0
    permute := (wordSemEnvToList (.ln : Spt (WordLocW width)) s.permute).2
    stackMax := (pushEnv (.ln, .ln) none s).stackMax }
  have hS0 : setStore .allocSize (.word c)
      { pushEnv (.ln, .ln) none s with locals := .ln, localsSize := some 0 } =
      { setStore .allocSize (.word c) B' with
        stack := .stackFrame s.localsSize [] [] none :: (setStore .allocSize (.word c) B').stack } := by
    simp only [setStore, pushEnv, htoal, henv, B']
  rw [hS0] at halloc
  rcases hgc : gc { setStore .allocSize (.word c) B' with
      stack := .stackFrame s.localsSize [] [] none :: (setStore .allocSize (.word c) B').stack }
      with _ | s2
  · simp only [hgc, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hgc] at halloc
  rcases hpop : popEnv s2 with _ | y
  · simp only [hpop, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hpop] at halloc
  obtain ⟨hyl, hgcB⟩ := wordGcEmptyFrame _ s2 y s.localsSize ⟨hgc, hpop⟩
  -- the popped frame restores the original size prediction
  have hkey := WordSemStackEq.gcSKeyEq _ _ hgc
  have hyls : y.localsSize = s.localsSize := by
    simp only at hkey
    simp only [popEnv] at hpop
    rcases hst : s2.stack with _ | ⟨⟨n', l0', l', opt'⟩, rest⟩
    · rw [hst] at hkey; simp [sKeyEq] at hkey
    rw [hst] at hkey hpop
    rcases opt' with _ | ⟨h1, _, _⟩
    · simp only [sKeyEq, sFrameKeyEq] at hkey
      simp only [Option.some.injEq] at hpop
      rw [← hpop]
      exact hkey.2.2.2.symm
    · simp [sKeyEq, sFrameKeyEq] at hkey
  -- B' is related to t
  have hrel' := hrel
  unfold stateRel at hrel'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, -,
    r37, r38, -⟩ := hrel'
  have hB' : stateRel ac k 0 0 B' t lens 0 := by
    unfold stateRel
    refine ⟨r1, r2, ?_, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      sptWf_ln, ?_, r38, ?_⟩
    · show (wordSemEnvToList (.ln : Spt (WordLocW width)) s.permute).2 = fun _ => id
      simp [wordSemEnvToList, r3]
    · obtain ⟨-, rlim, rmax⟩ := r37
      refine ⟨by simp, rlim, ?_⟩
      intro m hm
      simp only [B', pushEnv, wordSemOptionMax] at hm
      split at hm
      · rename_i a b ha hb
        simp only [Option.some.injEq] at hm
        obtain ⟨hle, -, size, hsize, hsz⟩ := rmax a ha
        exact ⟨by omega, rfl, size, hsize, hsz⟩
      · cases hm
    · intro n v hn
      change sptLookup n Spt.ln = some v at hn
      simp [sptLookup] at hn
  have hsetB := AllocSimulation.stateRelSetStore0 ac k B' t lens 0 (.word c) hB'
  obtain ⟨t2, ht2gc, hR2, ht2len, ht2sp⟩ :=
    GcSimulation.gcStateRel ac k _ _ _ lens ⟨hgcB, hsetB⟩
  have hymax := (gc_stackMax hgcB).1
  have hR2' := hR2
  unfold stateRel at hR2'
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, -,
    g37, g38, -⟩ := hR2'
  have hy : stateRel ac k 0 0 y t2 lens 0 := by
    unfold stateRel
    refine ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
      g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35,
      by rw [hyl]; exact sptWf_ln, ?_, g38, ?_⟩
    · obtain ⟨-, glim, gmax⟩ := g37
      refine ⟨by simp, glim, ?_⟩
      intro m hm
      obtain ⟨hle, -, size, hsize, hsz⟩ := gmax m hm
      refine ⟨hle, ?_, size, hsize, hsz⟩
      rw [hyls]
      have hm' : (pushEnv (.ln, .ln) none s).stackMax = some m := by
        rw [← hm]; exact hymax.symm
      simp only [pushEnv, wordSemOptionMax] at hm'
      split at hm'
      · rename_i a b ha hb
        exact (r37.2.2 a ha).2.1
      · cases hm'
    · intro n v hn
      rw [hyl] at hn
      simp [sptLookup] at hn
  have hstore : y.store = t2.store.eraseEq .handler := by
    unfold stateRel at hy; exact hy.2.2.2.2.2.2.2.2.2.2.2.1
  have hclock : y.clock = t2.clock := by
    unfold stateRel at hy; exact hy.1
  have hffi : t2.ffi = y.ffi := by
    unfold stateRel at hy; exact hy.2.2.2.1
  have hget : getStore .allocSize y = t2.store.lookup .allocSize := by
    simp [getStore, hstore, HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
  rw [hget] at halloc
  rcases hw : t2.store.lookup .allocSize with _ | w
  · simp only [hw, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  simp only [hw] at halloc
  rw [hasSpace_eraseHandler y t2.store hstore] at halloc
  rcases hb : StackSemAllocation.hasSpace w t2.store with _ | _ | _
  · simp only [hb, Prod.mk.injEq] at halloc
    exact absurd halloc.1.symm hnerr
  · simp only [hb, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    refine ⟨StackSemStateOps.emptyEnv t2, some (.halt (.word 1)),
      by simp only [StackSemAllocation.alloc, ht2gc, hw, hb], ?_⟩
    simp only [reduceCtorEq, if_false, true_and]
    exact ⟨hclock, hffi.symm⟩
  · simp only [hb, Prod.mk.injEq] at halloc
    obtain ⟨rfl, rfl⟩ := halloc
    refine ⟨t2, none, by simp only [StackSemAllocation.alloc, ht2gc, hw, hb], ?_⟩
    simp only [if_true, true_and]
    exact ⟨hy, by rw [ht2len]; rfl, by rw [ht2sp]; rfl⟩

end Flapjack.WordToStackProofs.AllocStateRel
