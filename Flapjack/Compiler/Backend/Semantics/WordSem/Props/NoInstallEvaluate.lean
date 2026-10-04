import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode

/-!
# wordProps no-install/no-alloc code-map family

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4690-4757`
(bead `flapjack-pxn.18.5.15.3.27.1.1.4.6`): `no_alloc_code_def`,
`no_alloc_find_code`, `no_install_find_code` and
`no_install_evaluate_const_code`.  HOL's `no_install p` and `no_alloc p` are
the tagged Boolean `noInstallSubprogsHOL p = true` and
`noAllocSubprogsHOL p = true`; `no_install_code_def` is the existing tagged
`WordProps.noInstallCode`.

HOL proves `no_install_evaluate_const_code` by `recInduct evaluate_ind`.
Here it follows from an untagged recursion on HOL's termination measure, as
for `evaluate_stack_max_le`, whose motive carries the two `no_install`
premises; each recursive call receives exactly the premises HOL's induction
hypotheses discharge (`no_install` of the sub-program, from `no_install_def`
or `no_install_find_code`, and `no_install_code` of the intermediate code
map, from the earlier calls).  The primitive cases use `alloc_const`,
`inst_const_full`, `mem_store_const`, `jump_exc_const`, `share_inst_const`,
`pop_env_const` and `cut_state_const`, as HOL does.

Inherited assumption: `evaluate`'s `Inst` clause calls the tagged `inst`,
which carries `(reals_as_rational_cuts)`; the evaluator theorem records the
inherited `docs/SOUNDNESS.md` item 8 assumption in the theorem map.
-/

namespace Flapjack

namespace WordSemNoInstallEvaluateSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemNoInstallEvaluateSupport

namespace WordProps

/-- Exact HOL `no_alloc_code_def` (`wordPropsScript.sml:4690-4693`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def noAllocCode {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (k n : Nat) (p : WordLangProgHOL (BitVec width)),
    sptLookup k code = some (n, p) → noAllocSubprogsHOL p = true

/-- Both `find_code` branches return a body looked up in `code`. -/
theorem findCode_lookup {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (dest : Option Nat)
    (args : List (WordLocW width)) (lsize : Spt Nat) (args1 : List (WordLocW width))
    (expr : WordLangProgHOL (BitVec width)) (ps : Option Nat)
    (h : wordSemFindCode dest args code lsize = some (args1, expr, ps)) :
    ∃ k n, sptLookup k code = some (n, expr) := by
  cases dest with
  | some p =>
    simp only [wordSemFindCode] at h
    split at h
    · cases h
    · rename_i arity e he
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        exact ⟨p, arity, he⟩
      · cases h
  | none =>
    simp only [wordSemFindCode] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · rename_i he
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl, -⟩ := h
            exact ⟨_, _, he⟩
          · cases h
      · cases h

/-- Exact HOL `no_alloc_find_code` (`wordPropsScript.sml:4695-4705`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem noAllocFindCode {width : Nat} [NeZero width] :
    ∀ (code : Spt (Nat × WordLangProgHOL (BitVec width))) (dest : Option Nat)
      (args : List (WordLocW width)) (lsize : Spt Nat) (args1 : List (WordLocW width))
      (expr : WordLangProgHOL (BitVec width)) (ps : Option Nat),
      wordSemFindCode dest args code lsize = some (args1, expr, ps) ∧ noAllocCode code →
        noAllocSubprogsHOL expr = true := by
  intro code dest args lsize args1 expr ps ⟨h, hc⟩
  obtain ⟨k, n, hk⟩ := findCode_lookup code dest args lsize args1 expr ps h
  exact hc k n expr hk

/-- Exact HOL `no_install_find_code` (`wordPropsScript.sml:4712-4720`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem noInstallFindCode {width : Nat} [NeZero width] :
    ∀ (code : Spt (Nat × WordLangProgHOL (BitVec width))) (dest : Option Nat)
      (args : List (WordLocW width)) (lsize : Spt Nat) (args1 : List (WordLocW width))
      (expr : WordLangProgHOL (BitVec width)) (ps : Option Nat),
      noInstallCode code ∧ wordSemFindCode dest args code lsize = some (args1, expr, ps) →
        noInstallSubprogsHOL expr = true := by
  intro code dest args lsize args1 expr ps ⟨hc, h⟩
  obtain ⟨k, n, hk⟩ := findCode_lookup code dest args lsize args1 expr ps h
  exact hc k n expr hk

end WordProps

namespace WordSemStateFiniteExact

open WordProps

section Evaluate

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem code_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : (alloc w names s).2.code = s.code :=
  (allocConst w names s (alloc w names s).2 (alloc w names s).1 rfl).2.2.1

theorem code_shareInst (op : WordMemOp) (v : Nat) (c : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    (shareInst (rw := width) op v c s).2.code = s.code :=
  (shareInstConst op v c s _ _ rfl).2.2.2.2.1

set_option linter.unusedSimpArgs false in
/-- Every statement that neither recurses nor reads the clock keeps `code`,
    except `Install`, which `no_install` excludes. -/
theorem code_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true)
    (hni : noInstallSubprogsHOL p = true) :
    (evaluate p s).2.code = s.code := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | rfl
      | exact code_alloc _ _ _
      | exact code_shareInst _ _ _ _
      | (rename_i h; exact (instConstFull _ _ _ h).1)
      | (rename_i h; exact (memStoreConst _ _ _ _ h).2.2.2.2.2.2.2.2.1)
      | (rename_i h; exact (jumpExcConst _ _ _ h).2.2.2.2.1)
      | (simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni)

theorem code_pushEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : (pushEnv envs handler s).code = s.code := by
  rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl

theorem noInstall_call_ret {n : List Nat} {names : WordLangCutsetsHOL}
    {r : WordLangProgHOL (BitVec width)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    (hni : noInstallSubprogsHOL (.call (some (n, names, r, l1, l2)) dest args h) = true) :
    noInstallSubprogsHOL r = true := by
  unfold noInstallSubprogsHOL notCreatedSubprogsWithMemOp at hni
  simp only [Bool.and_eq_true] at hni
  exact hni.1.2

theorem noInstall_call_handler {ret : Option (List Nat × WordLangCutsetsHOL ×
      WordLangProgHOL (BitVec width) × Nat × Nat)}
    {dest : Option Nat} {args : List Nat} {n : Nat} {hp : WordLangProgHOL (BitVec width)}
    {l1 l2 : Nat}
    (hni : noInstallSubprogsHOL (.call ret dest args (some (n, hp, l1, l2))) = true) :
    noInstallSubprogsHOL hp = true := by
  unfold noInstallSubprogsHOL notCreatedSubprogsWithMemOp at hni
  simp only [Bool.and_eq_true] at hni
  exact hni.2.2

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `no_install_evaluate_const_code`, by recursion on
    HOL's termination measure.  Each recursive call is given exactly the
    `no_install` premises of HOL's matching induction hypothesis. -/
theorem code_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      noInstallSubprogsHOL p = true → noInstallCode s.code → (evaluate p s).2.code = s.code
  | .tick, s, _, _ => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> rfl
  | .mustTerminate q, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.true_and] at hni
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]
      · simp only [hz, dite_false, if_false]
        have ih := code_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hni hc
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => exact ih
        | some x => cases x <;> first | rfl | exact ih
  | .seq c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      have ih1 := code_evaluate c1 s hni.1 hc
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1
      have hc1 := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        have hc' : noInstallCode s1.code := ih1 ▸ hc
        exact (code_evaluate c2 s1 hni.2 hc').trans ih1
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at hni
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;>
        first | rfl | exact code_evaluate c1 s hni.1 hc | exact code_evaluate c2 s hni.2 hc
  | .loop names c exitNames, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hni' := hni
      rw [ht]
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hni'
      rcases hcs : cutState (names, .ln) s with _ | s'
      · rfl
      simp only
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := code_evaluate c { s with locals := l } hni' hc
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at ih
      have hcl := evaluate_clock c _ rb s1 hb
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true]
          exact ih
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          have hcd : noInstallCode (decClock s1).code := ih ▸ hc
          exact (code_evaluate (.loop names c exitNames) (decClock s1) hni hcd).trans ih
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact ih
          · rename_i s2 hce
            obtain ⟨_, rfl⟩ := cutStateConst _ _ _ hce
            exact ih
        · exact ih
  | .call ret dest args handler, s, hni, hc => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · rfl
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · rfl
      simp only
      have hprog := noInstallFindCode s.code dest _ _ _ prog _ ⟨hc, hf⟩
      cases ret with
      | none =>
        cases handler with
        | some _ => rfl
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true]; rfl
          simp only [hz, dite_false, if_false]
          have ih := code_evaluate prog (callEnv args1 ss (decClock s)) hprog hc
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          simp only
          split
          · exact ih
          · exact ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · rfl
        simp only
        by_cases hz : s.clock = 0
        · simp only [hz, dite_true, if_true]; rfl
        simp only [hz, dite_false, if_false]
        have hpre : (callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code :=
          code_pushEnv envs handler _
        have ih := code_evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
          hprog (hpre ▸ hc)
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih
        have hcl := evaluate_clock prog _ rc s2 hcv
        have h2 : s2.code = s.code := ih.trans hpre
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · exact h2
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]; exact h2
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · exact h2
          simp only
          have h3 : s1.code = s.code := ((popEnvConst _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · have hcs1 : noInstallCode (setVars n ys s1).code := h3 ▸ hc
            exact (code_evaluate retHandler (setVars n ys s1) (noInstall_call_ret hni) hcs1).trans h3
          · exact h3
        · cases handler with
          | none => exact h2
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · exact h2
            · split
              · have hcs2 : noInstallCode (setVar n' y s2).code := h2 ▸ hc
                exact (code_evaluate hprog' (setVar n' y s2) (noInstall_call_handler hni) hcs2).trans h2
              · exact h2
        all_goals exact h2
  | .skip, s, hni, _ => code_evaluate_const s _ rfl hni
  | .move a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .inst a, s, hni, _ => code_evaluate_const s _ rfl hni
  | .assign a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .get a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .set a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .store a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .alloc a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .storeConsts a b c d f, s, hni, _ => code_evaluate_const s _ rfl hni
  | .raise a, s, hni, _ => code_evaluate_const s _ rfl hni
  | WordLangProgHOL.return a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | WordLangProgHOL.break a, s, hni, _ => code_evaluate_const s _ rfl hni
  | WordLangProgHOL.continue a, s, hni, _ => code_evaluate_const s _ rfl hni
  | .opCurrHeap a b c, s, hni, _ => code_evaluate_const s _ rfl hni
  | .locValue a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .install a b c d f, s, hni, _ => code_evaluate_const s _ rfl hni
  | .codeBufferWrite a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .dataBufferWrite a b, s, hni, _ => code_evaluate_const s _ rfl hni
  | .ffi a b c d f g, s, hni, _ => code_evaluate_const s _ rfl hni
  | .shareInst a b c, s, hni, _ => code_evaluate_const s _ rfl hni
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

end Evaluate

/-- Exact HOL `no_install_evaluate_const_code` (`wordPropsScript.sml:4722-4757`):
    for an arbitrary program, state, result and post-state, the conjunctive
    premise `evaluate (prog,s) = (result,s1) ∧ no_install prog ∧
    no_install_code s.code` gives `s.code = s1.code`.  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem noInstallEvaluateConstCode {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (result : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F),
      evaluate prog s = (result, s1) ∧ noInstallSubprogsHOL prog = true ∧
        noInstallCode s.code →
        s.code = s1.code := by
  intro prog s result s1 ⟨h, hni, hc⟩
  have := code_evaluate prog s hni hc
  rw [h] at this
  exact this.symm

end WordSemStateFiniteExact

end Flapjack
