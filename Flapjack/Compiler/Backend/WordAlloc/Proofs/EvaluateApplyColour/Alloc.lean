import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.PushPopEnv
import Flapjack.Compiler.Backend.WordAlloc.Proofs.KeyRemap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ScopedInjection
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap

/-!
# `evaluate_apply_colour` Alloc case

HOL `Resume evaluate_apply_colour[Alloc]` (`word_allocProofScript.sml`): the
cut-set restriction is simulated by `cut_envs_lemma`, the permutation oracle is
chosen by `push_env_s_val_eq`, the garbage collector is related by
`gc_s_val_eq_gen`, and the popped environments by `s_key_eq_val_eq_pop_env`
and `push_env_pop_env_s_key_eq`.

Only `evaluateApplyColour_Alloc` carries a HOL tag. Every other theorem here
(`sptAListLookup_eq_keyLookup`, `popEnvFields`, `popEnvHandlerNone`, the
association-list lemmas, `allocLocalsRel` and `allocSim`) is Flapjack proof
factoring or representation infrastructure for that single HOL case, not an
independent HOL original.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact WordSemStackEq

namespace EvaluateApplyColourAllocWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourAllocWitnesses

open EvaluateApplyColourAllocWitnesses

/-- Representation bridge (Flapjack infrastructure, no HOL original): the Spt
library's first-match `sptAListLookup` and the classical-equality `keyLookup`
used by the tagged `ALOOKUP_key_remap` ports are the same HOL `ALOOKUP`. -/
theorem sptAListLookup_eq_keyLookup {α : Type} (k : Nat) :
    ∀ l : List (Nat × α), sptAListLookup k l = keyLookup l k
  | [] => by simp [sptAListLookup, keyLookup, holAlookup]
  | (a, v) :: l => by
      have ih := sptAListLookup_eq_keyLookup k l
      unfold keyLookup at ih ⊢
      by_cases h : k = a
      · subst h; simp [sptAListLookup, holAlookup]
      · have h' : ¬ a = k := fun e => h e.symm
        simp only [sptAListLookup, holAlookup, if_neg h, if_neg h', ih]

/-- Field preservation of `pop_env` (Flapjack infrastructure). -/
theorem popEnvFields {width : Nat} [NeZero width] {C F : Type}
    {s y : WordSemStateFiniteExact width C F} (h : popEnv s = some y) :
    y.fpRegs = s.fpRegs ∧ y.store = s.store ∧ y.stackLimit = s.stackLimit ∧
    y.stackMax = s.stackMax ∧ y.stackSize = s.stackSize ∧ y.memory = s.memory ∧
    y.mdomain = s.mdomain ∧ y.shMdomain = s.shMdomain ∧ y.gcFun = s.gcFun ∧
    y.clock = s.clock ∧ y.code = s.code ∧ y.ffi = s.ffi ∧ y.be = s.be ∧
    y.termdep = s.termdep ∧ y.compile = s.compile ∧ y.compileOracle = s.compileOracle ∧
    y.codeBuffer = s.codeBuffer ∧ y.dataBuffer = s.dataBuffer := by
  unfold popEnv at h
  split at h <;> (try cases h) <;> simp_all

/-- `pop_env` with a handler-free top frame keeps the handler. -/
theorem popEnvHandlerNone {width : Nat} [NeZero width] {C F : Type}
    {s y : WordSemStateFiniteExact width C F} {m : Option Nat}
    {e0 e : List (Nat × WordLocW width)} {xs : List (WordSemStackFrame width)}
    (hst : s.stack = .stackFrame m e0 e none :: xs) (h : popEnv s = some y) :
    y.handler = s.handler ∧ y.localsSize = m ∧ y.stack = xs := by
  unfold popEnv at h
  rw [hst] at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩


/-- `ALOOKUP` succeeds exactly on the listed keys (Flapjack infrastructure). -/
private theorem alistLookupIsSomeA {α : Type} (k : Nat) :
    ∀ l : List (Nat × α), (sptAListLookup k l).isSome = true ↔ k ∈ l.map Prod.fst
  | [] => by simp [sptAListLookup]
  | (a, v) :: l => by
      by_cases h : k = a
      · subst h; simp [sptAListLookup]
      · simp [sptAListLookup, h, alistLookupIsSomeA k l]

/-- A key of a zipped list with enough values is found (Flapjack
infrastructure for HOL's `MEM_ZIP`/`ALOOKUP_MEM` reasoning). -/
private theorem alistLookupZipSome {α : Type} :
    ∀ (keys : List Nat) (vs : List α) (k : Nat), k ∈ keys → keys.length ≤ vs.length →
      (sptAListLookup k (keys.zip vs)).isSome = true
  | [], _, _, h, _ => by simp at h
  | a :: keys, [], _, _, h => by simp at h
  | a :: keys, v :: vs, k, hk, hl => by
      simp only [List.zip_cons_cons, sptAListLookup]
      by_cases h : k = a
      · simp [h]
      · simp only [h, if_false]
        exact alistLookupZipSome keys vs k (by simpa [h] using hk) (by simpa using hl)

/-- Local list-pair reassembly infrastructure used by this proof;
not a separately claimed HOL theorem port. -/
private theorem zipFstSnd' {α β : Type} (e : List (α × β)) :
    (e.map Prod.fst).zip (e.map Prod.snd) = e := by
  induction e with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- The popped-locals relation of the Alloc case (HOL's `ALOOKUP_key_remap_INJ`
step): renamed GC-list keys and the injective colouring transport every source
lookup to the coloured environment. -/
theorem allocLocalsRel {width : Nat} [NeZero width] (f : Nat → Nat)
    (x0 y1 : Spt (WordLocW width)) (keysB : List Nat) (l : List (Nat × WordLocW width))
    (hl : l.map Prod.fst = keysB.map f)
    (hinjK : ∀ a b, (a ∈ keysB ∨ sptDomain x0 a) → (b ∈ keysB ∨ sptDomain x0 b) →
      f a = f b → a = b)
    (hrx0 : strongLocalsRel f (sptDomain x0) x0 y1) (live : Nat → Prop) :
    strongLocalsRel f live
      (sptUnion (sptFromAList (keysB.zip (l.map Prod.snd))) (sptFromAList (sptToAList x0)))
      (sptUnion (sptFromAList l) (sptFromAList (sptToAList y1))) := by
  classical
  have hlen : keysB.length = l.length := by
    have := congrArg List.length hl; simpa using this.symm
  rintro k v ⟨-, h⟩
  rw [sptLookup_sptUnion, sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList] at h
  rw [sptLookup_sptUnion, sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]
  cases hA : sptAListLookup k (keysB.zip (l.map Prod.snd)) with
  | some v' =>
      rw [hA] at h
      simp only [Option.some.injEq] at h
      subst h
      have hk : k ∈ keysB := by
        have hm := (alistLookupIsSomeA k _).mp (by rw [hA]; rfl)
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
        exact (List.of_mem_zip hp).1
      have hremap := alookupKeyRemapINJ f k keysB (l.map Prod.snd)
        ⟨fun a b ha hb hab => hinjK a b (ha.elim (fun e => Or.inl (e ▸ hk)) Or.inl)
          (hb.elim (fun e => Or.inl (e ▸ hk)) Or.inl) hab, by simp [hlen]⟩
      rw [← sptAListLookup_eq_keyLookup, ← sptAListLookup_eq_keyLookup, hA, ← hl, zipFstSnd']
        at hremap
      rw [← hremap]
  | none =>
      rw [hA] at h
      have hkx : sptDomain x0 k := by simp [sptDomain, h]
      have hnot : f k ∉ l.map Prod.fst := by
        rw [hl]
        intro hm
        obtain ⟨k', hk', hfk⟩ := List.mem_map.mp hm
        have hkk := hinjK k' k (Or.inl hk') (Or.inr hkx) hfk
        subst hkk
        have := alistLookupZipSome keysB (l.map Prod.snd) k' hk' (by simp [hlen])
        rw [hA] at this; cases this
      have hnone : sptAListLookup (f k) l = none := by
        cases hB : sptAListLookup (f k) l with
        | none => rfl
        | some w =>
            have := (alistLookupIsSomeA (f k) l).mp (by rw [hB]; rfl)
            exact absurd this hnot
      rw [hnone]
      exact hrx0 k v ⟨hkx, h⟩

/-- The Alloc simulation core: for related states, colour injective on the
two cut sets and the live-scoped relation on both, some source oracle makes
the source `alloc` either fail or agree with the coloured `alloc`. -/
theorem allocSim {width : Nat} [NeZero width] {C F : Type}
    (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (n1 n2 : NumSet)
    (c : BitVec width) (live : NumSet) (lt : List (NumSet × NumSet))
    (hs : wordStateEqRel st cst)
    (hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) → (sptDomain n1 b ∨ sptDomain n2 b) →
      f a = f b → a = b)
    (hrel1 : strongLocalsRel f (sptDomain n1) st.locals cst.locals)
    (hrel2 : strongLocalsRel f (sptDomain n2) st.locals cst.locals) :
    ∃ perm, (alloc c (n1, n2) { st with permute := perm }).1 ≠ some .error →
      (alloc c (n1, n2) { st with permute := perm }).1 =
          (alloc c (applyNummapsKey f (n1, n2)) cst).1 ∧
        wordStateEqRel (alloc c (n1, n2) { st with permute := perm }).2
          (alloc c (applyNummapsKey f (n1, n2)) cst).2 ∧
        applyColourLocals f live lt (alloc c (n1, n2) { st with permute := perm }).1
          (alloc c (n1, n2) { st with permute := perm }).2.locals
          (alloc c (applyNummapsKey f (n1, n2)) cst).2.locals := by
  classical
  have hinj1 : ∀ a b, sptDomain n1 a → sptDomain n1 b → f a = f b → a = b :=
    fun a b ha hb => hinj a b (Or.inl ha) (Or.inl hb)
  have hinj2 : ∀ a b, sptDomain n2 a → sptDomain n2 b → f a = f b → a = b :=
    fun a b ha hb => hinj a b (Or.inr ha) (Or.inr hb)
  cases hcut : wordSemCutEnvs (n1, n2) st.locals with
  | none =>
      refine ⟨st.permute, fun he => absurd ?_ he⟩
      unfold alloc
      have : wordSemCutEnvs (n1, n2) ({ st with permute := st.permute } :
          WordSemStateFiniteExact width C F).locals = none := hcut
      rw [this]
  | some xs =>
    obtain ⟨x0, x1⟩ := xs
    obtain ⟨y1, y2, hcut', hdy1, hdy2, hr1, hr2, hi1, hi2, hdx0, hdx1⟩ :=
      cutEnvsLemma n1 n2 st.locals cst.locals x0 x1 f ⟨hinj1, hinj2, hcut, hrel1, hrel2⟩
    have hh : cst.handler = st.handler := by
      unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.1
    have hstk : cst.stack = st.stack := by unfold wordStateEqRel at hs; exact hs.2.2.2.1
    have hls : cst.localsSize = st.localsSize := by unfold wordStateEqRel at hs; exact hs.2.2.1
    obtain ⟨perm, henv, hsv⟩ := pushEnvSValEq (setStore .allocSize (.word c) st)
      (setStore .allocSize (.word c) cst) x1 x0 y2 y1 f none none cst.permute
      ⟨hh.symm, hstk.symm, hls.symm, by rw [hdy2, hdx1], by rw [hdx1]; exact hinj2,
        by rw [hdy1, hdx0], by rw [hdx0]; exact hinj1, by rw [hdx1]; exact hr2, rfl⟩
    refine ⟨perm, fun he => ?_⟩
    unfold alloc at he ⊢
    have hcutP : wordSemCutEnvs (n1, n2) ({ st with permute := perm } :
        WordSemStateFiniteExact width C F).locals = some (x0, x1) := hcut
    rw [hcutP] at he ⊢
    rw [hcut']
    simp only at he ⊢
    have hs0 := hs
    unfold wordStateEqRel at hs0
    obtain ⟨efp, estore, _, _, eslim, esmax, essize, emem, emd, esmd, egc, _, eclk, ecode, effi,
      ebe, etd, ecomp, ecor, ecb, edb⟩ := hs0
    generalize hSd : pushEnv (x0, x1) none
      (setStore .allocSize (.word c) { st with permute := perm }) = S at he ⊢
    generalize hCd : pushEnv (y1, y2) none (setStore .allocSize (.word c) cst) = Cs at hsv ⊢
    have hsvS : sValEq S.stack Cs.stack := by rw [← hSd]; exact hsv
    cases hg : gc S with
    | none => rw [hg] at he; exact absurd rfl he
    | some X =>
    rw [hg] at he
    simp only at he ⊢
    obtain ⟨T', hgT, hsvXT, hskCT, hmXT, hstXT, hssXT, hsmXT, hslXT⟩ :=
      gcSValEqGen S Cs X ⟨by rw [← hSd, ← hCd]; simp [pushEnv, setStore, egc],
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, emem],
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, emd],
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, estore],
        hsvS,
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, essize],
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, esmax, hstk, hls, wordSemStackSize,
          wordSemStackSizeFrame],
        by rw [← hSd, ← hCd]; simp [pushEnv, setStore, eslim],
        hg⟩
    rw [hgT]
    simp only
    have hSst : S.stack = .stackFrame st.localsSize (sptToAList x0)
        (wordSemEnvToList x1 perm).1 none :: st.stack := by rw [← hSd]; rfl
    have hCst : Cs.stack = .stackFrame cst.localsSize (sptToAList y1)
        (wordSemEnvToList y2 cst.permute).1 none :: cst.stack := by rw [← hCd]; rfl
    have hkXS : sKeyEq X.stack S.stack := (sKeyEqSym _ _).mp (gcSKeyEq S X hg)
    cases hp : popEnv X with
    | none => rw [hp] at he; exact absurd rfl he
    | some XX =>
    rw [hp] at he
    simp only at he ⊢
    obtain ⟨lsz', ls', rest, hT'eq, hlocX, hskX, hsvX, hhX⟩ :=
      sKeyEqValEqPopEnv X XX st.localsSize (sptToAList x0) (wordSemEnvToList x1 perm).1 none
        st.stack T'.stack ⟨hp, hSst ▸ hkXS, hsvXT⟩
    obtain ⟨n_, l, ls, opt, hT'st, CXX, hpopC, hlocC, -, hskC⟩ :=
      pushEnvPopEnvSKeyEq (y1, y2) none (setStore .allocSize (.word c) cst) T'
        (by rw [hCd]; exact hskCT)
    rw [hT'st] at hT'eq
    simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq] at hT'eq
    obtain ⟨⟨rfl, -, rfl, rfl⟩, rfl⟩ := hT'eq
    rw [hpopC]
    simp only
    obtain ⟨pXfp, pXst, pXsl, pXsm, pXss, pXm, pXmd, pXsmd, pXgc, pXclk, pXcode, pXffi, pXbe,
      pXtd, pXcomp, pXco, pXcb, pXdb⟩ := popEnvFields hp
    obtain ⟨pCfp, pCst, pCsl, pCsm, pCss, pCm, pCmd, pCsmd, pCgc, pCclk, pCcode, pCffi, pCbe,
      pCtd, pCcomp, pCco, pCcb, pCdb⟩ := popEnvFields hpopC
    obtain ⟨gXfp, gXmd, gXsmd, gXgc, gXh, gXclk, gXcode, -, gXls, gXss, gXsm, gXsl, gXbe, gXffi,
      gXcomp, gXco, gXcb, gXdb, -, gXtd⟩ := gcFrame S X hg
    obtain ⟨gTfp, gTmd, gTsmd, gTgc, gTh, gTclk, gTcode, -, gTls, gTss, gTsm, gTsl, gTbe, gTffi,
      gTcomp, gTco, gTcb, gTdb, -, gTtd⟩ := gcFrame Cs T' hgT
    have hSf : S.fpRegs = st.fpRegs ∧ S.mdomain = st.mdomain ∧ S.shMdomain = st.shMdomain ∧
        S.gcFun = st.gcFun ∧ S.handler = st.handler ∧ S.clock = st.clock ∧ S.code = st.code ∧
        S.be = st.be ∧ S.ffi = st.ffi ∧ S.compile = st.compile ∧
        S.compileOracle = st.compileOracle ∧ S.codeBuffer = st.codeBuffer ∧
        S.dataBuffer = st.dataBuffer ∧ S.termdep = st.termdep := by
      rw [← hSd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hCf : Cs.fpRegs = cst.fpRegs ∧ Cs.mdomain = cst.mdomain ∧ Cs.shMdomain = cst.shMdomain ∧
        Cs.gcFun = cst.gcFun ∧ Cs.handler = cst.handler ∧ Cs.clock = cst.clock ∧
        Cs.code = cst.code ∧ Cs.be = cst.be ∧ Cs.ffi = cst.ffi ∧ Cs.compile = cst.compile ∧
        Cs.compileOracle = cst.compileOracle ∧ Cs.codeBuffer = cst.codeBuffer ∧
        Cs.dataBuffer = cst.dataBuffer ∧ Cs.termdep = cst.termdep := by
      rw [← hCd]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨hSfp, hSmd, hSsmd, hSgc, hSh, hSclk, hScode, hSbe, hSffi, hScomp, hSco, hScb, hSdb,
      hStd⟩ := hSf
    obtain ⟨hCfp, hCmd, hCsmd, hCgc, hCh, hCclk, hCcode, hCbe, hCffi, hCcomp, hCco, hCcb, hCdb,
      hCtd⟩ := hCf
    -- shape of the collected source stack
    have hXst : ∃ l0 lX restX, X.stack = .stackFrame st.localsSize l0 lX none :: restX := by
      rw [hSst] at hkXS
      cases hxs : X.stack with
      | nil => rw [hxs] at hkXS; exact absurd hkXS (by simp [sKeyEq])
      | cons fr restX =>
          rw [hxs] at hkXS
          rcases fr with ⟨m, l0, lX, hx⟩
          have hf := hkXS.2
          rw [sFrameKeyEqDef2] at hf
          obtain ⟨-, rfl, -, rfl⟩ := hf
          exact ⟨l0, lX, restX, rfl⟩
    obtain ⟨l0, lX, restX, hXst'⟩ := hXst
    obtain ⟨hXXh, hXXls, -⟩ := popEnvHandlerNone hXst' hp
    obtain ⟨hCXXh, hCXXls, hCXXst⟩ := popEnvHandlerNone hT'st hpopC
    have hW : wordStateEqRel XX CXX := by
      unfold wordStateEqRel
      have hstack : CXX.stack = XX.stack := by
        rw [hCXXst]
        have hk : sKeyEq XX.stack CXX.stack :=
          sKeyEqTrans _ _ _ ⟨hskX, by rw [← hstk]; exact hskC⟩
        rw [hCXXst] at hk
        exact (sValAndKeyEq _ _ ⟨hsvX, hk⟩).symm
      refine ⟨?_, ?_, ?_, hstack, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pCfp, gTfp, hCfp, efp, ← hSfp, ← gXfp, ← pXfp]
      · rw [pCst, hstXT, ← pXst]
      · rw [hCXXls, hXXls]
      · rw [pCsl, hslXT, ← pXsl]
      · rw [pCsm, hsmXT, ← pXsm]
      · rw [pCss, hssXT, ← pXss]
      · rw [pCm, hmXT, ← pXm]
      · rw [pCmd, gTmd, hCmd, emd, ← hSmd, ← gXmd, ← pXmd]
      · rw [pCsmd, gTsmd, hCsmd, esmd, ← hSsmd, ← gXsmd, ← pXsmd]
      · rw [pCgc, gTgc, hCgc, egc, ← hSgc, ← gXgc, ← pXgc]
      · rw [hCXXh, gTh, hCh, hh, ← hSh, ← gXh, hXXh]
      · rw [pCclk, gTclk, hCclk, eclk, ← hSclk, ← gXclk, ← pXclk]
      · rw [pCcode, gTcode, hCcode, ecode, ← hScode, ← gXcode, ← pXcode]
      · rw [pCffi, gTffi, hCffi, effi, ← hSffi, ← gXffi, ← pXffi]
      · rw [pCbe, gTbe, hCbe, ebe, ← hSbe, ← gXbe, ← pXbe]
      · rw [pCtd, gTtd, hCtd, etd, ← hStd, ← gXtd, ← pXtd]
      · rw [pCcomp, gTcomp, hCcomp, ecomp, ← hScomp, ← gXcomp, ← pXcomp]
      · rw [pCco, gTco, hCco, ecor, ← hSco, ← gXco, ← pXco]
      · rw [pCcb, gTcb, hCcb, ecb, ← hScb, ← gXcb, ← pXcb]
      · rw [pCdb, gTdb, hCdb, edb, ← hSdb, ← gXdb, ← pXdb]
    have hL : strongLocalsRel f (sptDomain live) XX.locals CXX.locals := by
      simp only [setStore] at henv
      rcases hy : wordSemEnvToList y2 cst.permute with ⟨lsC, pmC⟩
      rcases hx : wordSemEnvToList x1 perm with ⟨lsB, pmB⟩
      rw [hy, hx] at henv
      obtain ⟨-, hmapB, -⟩ := henv
      have hkCT := hskCT
      rw [hCst, hT'st, hy] at hkCT
      have hf := hkCT.2
      rw [sFrameKeyEqDef2] at hf
      have hl' : l.map Prod.fst = (lsB.map Prod.fst).map f := by
        rw [← hf.1, ← hmapB, List.map_map, List.map_map]; rfl
      have hkeys := envToListKeys x1 perm
      rw [hx] at hkeys
      rw [hlocX, hlocC]
      rw [hx]
      refine allocLocalsRel f x0 y1 (lsB.map Prod.fst) l hl' ?_ (by rw [hdx0]; exact hr1) _
      have hmem : ∀ a, (a ∈ lsB.map Prod.fst ∨ sptDomain x0 a) → (sptDomain n1 a ∨ sptDomain n2 a) := by
        intro a ha
        rcases ha with ha | ha
        · have : sptDomain x1 a := by rw [← hkeys]; exact ha
          rw [hdx1] at this; exact Or.inr this
        · rw [hdx0] at ha; exact Or.inl ha
      exact fun a b ha hb hab => hinj a b (hmem a ha) (hmem b hb) hab
    have hstoreXC : CXX.store = XX.store := by rw [pCst, hstXT, ← pXst]
    have hgs : getStore .allocSize CXX = getStore .allocSize XX := by
      simp only [getStore, hstoreXC]
    have hsp : ∀ w, hasSpace w CXX = hasSpace w XX := by
      intro w; simp only [hasSpace, getStore, hstoreXC]
    rw [hgs]
    cases hga : getStore .allocSize XX with
    | none => rw [hga] at he; exact absurd rfl he
    | some w =>
      rw [hga] at he
      simp only at he ⊢
      rw [hsp]
      cases hhs : hasSpace w XX with
      | none => rw [hhs] at he; exact absurd rfl he
      | some b =>
        cases b
        · exact ⟨rfl, wsrFlush true hW, rfl⟩
        · exact ⟨rfl, hW, hL⟩

/-- HOL `evaluate_apply_colour`, `Alloc` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateApplyColour_Alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (names : WordLangCutsetsHOL) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.alloc n names : WordLangProgHOL (BitVec width)) live lt ∧
        wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.alloc n names : WordLangProgHOL (BitVec width))
          live lt)) st.locals cst.locals →
      applyColourPost f (.alloc n names : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  obtain ⟨n1, n2⟩ := names
  simp only [colouringOk, getLive] at hok hr
  have hevS : ∀ q : Nat → Nat → Nat,
      evaluate (.alloc n (n1, n2) : WordLangProgHOL (BitVec width)) { st with permute := q } =
        match getVar n st with
        | some (.word w) => alloc w (n1, n2) { st with permute := q }
        | _ => (some .error, { st with permute := q }) := by
    intro q; rw [evaluate]; rfl
  cases hv : getVar n st with
  | none =>
      apply applyColourPost_self
      intro he
      rw [evaluate, hv] at he
      exact absurd rfl he
  | some x =>
    cases x with
    | loc _ _ =>
        apply applyColourPost_self
        intro he
        rw [evaluate, hv] at he
        exact absurd rfl he
    | word c =>
      have hcv := strongLocalsRelGetVar f _ st cst n (.word c)
        ⟨hr, (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hv⟩
      have hdom : ∀ a, (sptDomain n1 a ∨ sptDomain n2 a) →
          sptDomain (sptInsert n () (sptUnion n1 n2)) a := fun a ha =>
        (sptDomain_ins _ _ _ a).mpr (Or.inr ((sptDomain_uni _ _ a).mpr ha))
      obtain ⟨perm, hsim⟩ := allocSim st cst f n1 n2 c live lt hs
        (fun a b ha hb hab => hok.1 a b (hdom a ha) (hdom b hb) hab)
        (slrMono hr (fun k hk => hdom k (Or.inl hk)))
        (slrMono hr (fun k hk => hdom k (Or.inr hk)))
      refine applyColourPost_intro f _ live lt st cst perm _
        (alloc c (applyNummapsKey f (n1, n2)) cst).1 _
        (alloc c (applyNummapsKey f (n1, n2)) cst).2 (by rw [hevS, hv]) ?_
      intro he
      refine ⟨?_, hsim he⟩
      simp only [applyColour]
      rw [evaluate, hcv]

end Flapjack.WordAlloc
