import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-!
# HOL `wordSem` clock lemmas

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:1264-1365`
(bead `flapjack-h29l.9.1`): the clock never increases and `termdep` is
preserved by `gc`, `alloc`, `sh_mem_set_var`, `share_inst`, `inst` and
`evaluate`, and hence `fix_clock s (evaluate (c1, s)) = evaluate (c1, s)`.
-/

namespace Flapjack

namespace WordSemEvaluateClockSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateClockSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `gc_clock` (`wordSemScript.sml:1264-1270`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gc_clock {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s1 s2 : WordSemStateFiniteExact width C F),
      gc s1 = some s2 → s2.clock ≤ s1.clock ∧ s2.termdep = s1.termdep := by
  intro s1 s2 h
  unfold gc at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨Nat.le_refl _, rfl⟩

/-- Exact HOL `alloc_clock` (`wordSemScript.sml:1272-1286`).  HOL binds an
    unused variable `xs : 'a`; it is kept here, with its type variable as `α`.
    HOL's free variables `x` and `names` are parameters. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem alloc_clock {width : Nat} [NeZero width] {C : Type} {F : Type} {α : Type}
    (x : BitVec width) (names : WordLangCutsetsHOL) :
    ∀ (_xs : α) (s1 : WordSemStateFiniteExact width C F) (vs : Option (WordSemResult width))
      (s2 : WordSemStateFiniteExact width C F),
      alloc x names s1 = (vs, s2) → s2.clock ≤ s1.clock ∧ s2.termdep = s1.termdep := by
  intro _ s1 vs s2 h
  unfold alloc at h
  split at h
  · cases h; exact ⟨Nat.le_refl _, rfl⟩
  · rename_i envs _
    split at h
    · cases h; exact ⟨Nat.le_refl _, rfl⟩
    · rename_i sg hg
      have ⟨hg1, hg2⟩ := gc_clock _ _ hg
      have hpc : (pushEnv envs none (setStore .allocSize (.word x) s1)).clock = s1.clock := by
        rw [pushEnv_clock]; rfl
      have hpt : (pushEnv envs none (setStore .allocSize (.word x) s1)).termdep = s1.termdep := by
        rw [pushEnv_termdep]; rfl
      split at h
      · cases h; simp only [flushState]; omega
      · rename_i sp hp
        have hp1 := popEnv_clock _ _ hp
        have hp2 := popEnv_termdep _ _ hp
        split at h
        · cases h; omega
        · split at h
          · cases h; omega
          · cases h; omega
          · cases h; simp only [flushState]; omega

/-- Exact HOL `sh_mem_set_var_clock` (`wordSemScript.sml:1288-1297`).  HOL's
    `v2 : 'd result option` has its own word type, here the width `rw`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem sh_mem_set_var_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    {rw : Nat} [NeZero rw] :
    ∀ (v : Nat) (s1 : WordSemStateFiniteExact width C F) (v2 : Option (WordSemResult rw))
      (s2 : WordSemStateFiniteExact width C F) (res : Option (HolFfiResult F)),
      shMemSetVar res v s1 = (v2, s2) → s2.clock ≤ s1.clock ∧ s2.termdep = s1.termdep := by
  intro v s1 v2 s2 res h
  rcases res with _ | ⟨_, _⟩ | _ <;>
    · simp only [shMemSetVar, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨Nat.le_refl _, rfl⟩

/-- Exact HOL `share_inst_clock` (`wordSemScript.sml:1299-1312`).  HOL's binder
    list keeps an unused `v1 : 'd` (here `δ`), and the result variable
    `v2 : 'e result option` is free in HOL, so it is a parameter here, with
    its own word type as the width `rw`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem share_inst_clock {width : Nat} [NeZero width] {C : Type} {F : Type} {δ : Type}
    {rw : Nat} [NeZero rw] (v2 : Option (WordSemResult rw)) :
    ∀ (op : WordMemOp) (v : Nat) (ad : BitVec width) (s1 : WordSemStateFiniteExact width C F)
      (_v1 : δ) (s2 : WordSemStateFiniteExact width C F),
      shareInst op v ad s1 = (v2, s2) → s2.clock ≤ s1.clock ∧ s2.termdep = s1.termdep := by
  intro op v ad s1 _ s2 h
  cases op <;> simp only [shareInst] at h
  all_goals first
    | exact sh_mem_set_var_clock _ _ _ _ _ h
    | (split at h
       · rename_i w _
         first
           | (unfold shMemStore at h)
           | (unfold shMemStoreByte at h)
           | (unfold shMemStore16 at h)
           | (unfold shMemStore32 at h)
         split at h
         · split at h <;>
             · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
               exact ⟨Nat.le_refl _, rfl⟩
         · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
           exact ⟨Nat.le_refl _, rfl⟩
       · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
         exact ⟨Nat.le_refl _, rfl⟩)

theorem memStore_clock_termdep {width : Nat} [NeZero width] {C : Type} {F : Type}
    {a : BitVec width} {w : WordLocW width} {s s1 : WordSemStateFiniteExact width C F}
    (h : memStore a w s = some s1) : s1.clock = s.clock ∧ s1.termdep = s.termdep := by
  unfold memStore at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- Exact HOL local `inst_clock` (`wordSemScript.sml:1314-1322`): binders,
    hypothesis and conclusion as in HOL.  Inherited assumption (bead
    `flapjack-qfld`): the statement is over the tagged `inst`, which carries
    `(reals_as_rational_cuts)` for its `FPSqrt` rendering; the theorem map
    records the inherited `docs/SOUNDNESS.md` item 8 assumption.  Clock
    preservation holds for that clause exactly as in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem inst_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (s s2 : WordSemStateFiniteExact width C F) :
    inst i s = some s2 → s2.clock ≤ s.clock ∧ s2.termdep = s.termdep := by
  intro h
  unfold inst at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (cases h; exact ⟨Nat.le_refl _, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨Nat.le_refl _, rfl⟩)
    | (unfold assign at h; split at h
       · cases h
       · cases h; exact ⟨Nat.le_refl _, rfl⟩)
    | (rename_i heq; cases h
       have := memStore_clock_termdep heq
       exact ⟨Nat.le_of_eq this.1, this.2⟩)

/-- `jump_exc` preserves `clock` and `termdep`. -/
theorem jumpExc_clock_termdep {width : Nat} [NeZero width] {C : Type} {F : Type}
    {s s1 : WordSemStateFiniteExact width C F} {l1 l2 : Nat}
    (h : jumpExc s = some (s1, l1, l2)) : s1.clock = s.clock ∧ s1.termdep = s.termdep := by
  unfold jumpExc at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- The clock of a `fix_clock` result is the smaller of the two clocks. -/
theorem fixClock_snd_clock {width : Nat} [NeZero width] {C : Type} {F : Type} {β : Type}
    (s : WordSemStateFiniteExact width C F) (x : β × WordSemStateFiniteExact width C F) :
    (fixClock s x).2.clock = min s.clock x.2.clock := by
  unfold fixClock; simp only; split <;> omega

/-- `fix_clock` restores `termdep`. -/
theorem fixClock_snd_termdep {width : Nat} [NeZero width] {C : Type} {F : Type} {β : Type}
    (s : WordSemStateFiniteExact width C F) (x : β × WordSemStateFiniteExact width C F) :
    (fixClock s x).2.termdep = s.termdep := rfl

set_option linter.unusedSimpArgs false in
/-- The projection form of `evaluate_clock`, proved by recursion on HOL's
    termination measure `(termdep, clock, size)`.  Lean's generated
    `evaluate.induct` is not usable for this definition, so the proof
    recurses directly. -/
theorem evaluate_clock_proj {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    (evaluate p s).2.clock ≤ s.clock ∧ (evaluate p s).2.termdep = s.termdep := by
  rw [evaluate.eq_def]
  cases p
  all_goals dsimp only
  all_goals (repeat' split)
  all_goals (try simp only [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.unsetVar, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.flushState] at *)
  all_goals first
    | exact ⟨Nat.le_refl _, rfl⟩
    | exact ⟨Nat.le_refl _, trivial⟩
    | (constructor <;> first | omega | trivial | rfl)
    | (rename_i heq; have := alloc_clock (α := Unit) _ _ () _ _ _ heq; exact this)
    | (rename_i heq; have := inst_clock _ _ _ heq; exact this)
    | (rename_i heq; have := memStore_clock_termdep heq; exact ⟨Nat.le_of_eq this.1, this.2⟩)
    | (rename_i heq; have := jumpExc_clock_termdep heq; exact ⟨Nat.le_of_eq this.1, this.2⟩)
    | (exact share_inst_clock (δ := Unit) _ _ _ _ _ () _ (Prod.eta _).symm)
    | (exact alloc_clock (α := Unit) _ _ () _ _ _ (Prod.eta _).symm)
    | (rw [fixClock_snd_clock, fixClock_snd_termdep]; exact ⟨Nat.min_le_left _ _, rfl⟩)
    | (refine ⟨Nat.le_trans (evaluate_clock_proj _ _).1 ?_, (evaluate_clock_proj _ _).2.trans ?_⟩ <;>
        (try have := cutState_clock_termdep _ _ _ ‹cutState _ _ = some _›) <;>
        (try have := fixClock_IMP_LESS_EQ _ _ _ _ ‹fixClock _ _ = (_, _)›) <;>
        (try have := popEnv_clock _ _ ‹popEnv _ = some _›) <;>
        (try have := popEnv_termdep _ _ ‹popEnv _ = some _›) <;>
        (try simp only [fixClock_snd_clock, fixClock_snd_termdep, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
          pushEnv_clock, pushEnv_termdep, wordSemSTOP] at *) <;> first | omega | trivial)
    | ((try have := cutState_clock_termdep _ _ _ ‹cutState _ _ = some _›)
       (try have := fixClock_IMP_LESS_EQ _ _ _ _ ‹fixClock _ _ = (_, _)›)
       (try have := popEnv_clock _ _ ‹popEnv _ = some _›)
       (try have := popEnv_termdep _ _ ‹popEnv _ = some _›)
       (try simp only [fixClock_snd_clock, fixClock_snd_termdep, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
         pushEnv_clock, pushEnv_termdep] at *)
       constructor <;> first | omega | trivial)
    | (have h1 := cutState_clock_termdep _ _ _ ‹cutState (_, Spt.ln) (fixClock _ _).snd = some _›
       have h2 := cutState_clock_termdep _ _ _ ‹cutState (_, Spt.ln) s = some _›
       simp only [fixClock_snd_clock, fixClock_snd_termdep] at h1
       constructor <;> omega)
termination_by (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (have := cutState_clock_termdep _ _ _ ‹cutState _ _ = some _›)
    try (have := fixClock_IMP_LESS_EQ _ _ _ _ ‹fixClock _ _ = (_, _)›)
    try (have := popEnv_clock _ _ ‹popEnv _ = some _›)
    try (have := popEnv_termdep _ _ ‹popEnv _ = some _›)
    try simp only [fixClock_snd_clock, fixClock_snd_termdep, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
      pushEnv_clock, pushEnv_termdep, wordSemSTOP, true_and] at *
    omega

/-- Exact HOL `evaluate_clock` (`wordSemScript.sml:1324-1355`):
    `evaluate (xs, s1) = (vs, s2) ⇒ s2.clock ≤ s1.clock ∧ s2.termdep =
    s1.termdep`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_clock {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (xs : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (vs : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate xs s1 = (vs, s2) → s2.clock ≤ s1.clock ∧ s2.termdep = s1.termdep := by
  intro xs s1 vs s2 h
  have := evaluate_clock_proj xs s1
  rw [h] at this
  exact this

/-- Exact HOL local `fix_clock_evaluate` (`wordSemScript.sml:1357-1363`):
    `fix_clock s (evaluate (c1, s)) = evaluate (c1, s)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fix_clock_evaluate {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (c1 : WordLangProgHOL (BitVec width)) :
    fixClock s (evaluate c1 s) = evaluate c1 s := by
  have ⟨h1, h2⟩ := evaluate_clock_proj c1 s
  generalize evaluate c1 s = r at h1 h2
  obtain ⟨res, s2⟩ := r
  unfold fixClock
  simp only at h1 h2 ⊢
  rw [if_neg (by omega)]
  cases s2
  simp only at h2 ⊢
  rw [h2]

end WordSemStateFiniteExact

end Flapjack
