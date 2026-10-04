import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.AllocConst
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConstFull
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.JumpExcConst
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.MemStoreConst
import Flapjack.Compiler.Backend.BackendProps
import Flapjack.Misc.MiscThe

/-!
# wordProps stack-limit and stack-maximum evaluator family

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4300-4441`
(bead `flapjack-pxn.18.5.15.3.27.1.1.4.2`), together with the two helper
results it uses from earlier in the script, `share_inst_const` (1161) and
`cut_state_const` (1293).  The evaluator theorems are over the native exact
`evaluate` with arbitrary programs, states, results and positive word width.

HOL proves `evaluate_stack_max_le` and `evaluate_stack_limit` by
`recInduct evaluate_ind`.  Here both are consequences of one untagged
recursion on HOL's termination measure (as for `evaluate_add_clock`), whose
motive is the conjunction of the two conclusions; each clause uses the same
helper facts as HOL's case (`gc_const`, `pop_env_const`, `push_env`,
`inst_const_full`, `mem_store_const`, `jump_exc_const`, `share_inst_const`,
`cut_state_const`, `call_env`).  HOL's `OPTION_MAP2 MAX` is the wordSem
helper `wordSemOptionMax`, equal to `Option.map₂ max`.

Inherited assumption: `evaluate`'s `Inst` clause calls the tagged `inst`,
which carries `(reals_as_rational_cuts)` for its `FPSqrt` rendering; the
evaluator theorems here record that inherited `docs/SOUNDNESS.md` item 8
assumption in the theorem map.  No numerical floating-point claim is made.
-/

namespace Flapjack

namespace WordSemEvaluateStackMaxSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateStackMaxSupport

namespace WordSemStateFiniteExact

open Flapjack.Compiler.Backend.BackendProps

section Helpers


/-- Exact HOL `share_inst_const` (`wordPropsScript.sml:1161-1180`): all
    fourteen original field conclusions of a `share_inst` step, for arbitrary
    operation, variable, address, result and states.  HOL's result type shares
    the word width `'a` of the state, so the result width is `width`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shareInstConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : WordMemOp) (v : Nat) (c : BitVec width)
    (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (h : shareInst op v c s = (res, s')) :
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.compile = s.compile ∧
    s'.compileOracle = s.compileOracle ∧
    s'.permute = s.permute ∧
    s'.clock = s.clock ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax := by
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] at h <;>
    (repeat' split at h) <;>
    (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
     simp [flushState, setVar])

/-- Exact HOL `cut_state_const` (`wordPropsScript.sml:1293-1299`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem cutStateConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordLangCutsetsHOL) (s s' : WordSemStateFiniteExact width C F)
    (h : cutState x s = some s') :
    ∃ l, s' = { s with locals := l } := by
  unfold cutState at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl⟩

theorem wordSemOptionMax_eq (n m : Option Nat) : wordSemOptionMax n m = Option.map₂ max n m := by
  rcases n with _ | _ <;> rcases m with _ | _ <;> rfl

/-- Exact HOL local `call_env_option_le_stack_max` (`wordPropsScript.sml:4298-4301`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callEnv_optionLe_stackMax {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (s : WordSemStateFiniteExact width C F) :
    optionLe s.stackMax (callEnv args1 ss s).stackMax := by
  simp only [callEnv, wordSemOptionMax_eq, optionLe_max_right]
  exact Or.inl (optionLe_refl _)

/-- Exact HOL local `call_push_env_option_le_stack_max`
    (`wordPropsScript.sml:4303-4310`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callPushEnv_optionLe_stackMax {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    optionLe s.stackMax (callEnv args1 ss (pushEnv envs handler s)).stackMax := by
  refine optionLe_trans _ _ _ ⟨?_, callEnv_optionLe_stackMax _ _ _⟩
  rcases handler with _ | ⟨_, _, _, _⟩ <;>
    simp only [pushEnv, wordSemOptionMax_eq, optionLe_max_right] <;>
    exact Or.inl (optionLe_refl _)

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The motive of the combined recursion: the stack limit is unchanged and
    the stack maximum only grows. -/
def StackRel (s t : WordSemStateFiniteExact width C F) : Prop :=
  t.stackLimit = s.stackLimit ∧ optionLe s.stackMax t.stackMax

theorem StackRel.refl (s : WordSemStateFiniteExact width C F) : StackRel s s :=
  ⟨rfl, optionLe_refl _⟩

theorem StackRel.trans {s t u : WordSemStateFiniteExact width C F}
    (h1 : StackRel s t) (h2 : StackRel t u) : StackRel s u :=
  ⟨h2.1.trans h1.1, optionLe_trans _ _ _ ⟨h1.2, h2.2⟩⟩

theorem StackRel.of_eq {s t : WordSemStateFiniteExact width C F}
    (h1 : t.stackLimit = s.stackLimit) (h2 : t.stackMax = s.stackMax) : StackRel s t :=
  ⟨h1, h2 ▸ optionLe_refl _⟩

theorem stackRel_pushEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : StackRel s (pushEnv envs handler s) := by
  refine ⟨by rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl, ?_⟩
  rcases handler with _ | ⟨_, _, _, _⟩ <;>
    simp only [pushEnv, wordSemOptionMax_eq, optionLe_max_right] <;>
    exact Or.inl (optionLe_refl _)

theorem stackRel_callEnv (args1 : List (WordLocW width)) (ss : Option Nat)
    (s : WordSemStateFiniteExact width C F) : StackRel s (callEnv args1 ss s) :=
  ⟨rfl, callEnv_optionLe_stackMax _ _ _⟩

theorem stackRel_popEnv {s t : WordSemStateFiniteExact width C F} (h : popEnv s = some t) :
    StackRel s t := by
  have := popEnvConst _ _ h
  exact StackRel.of_eq this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem stackRel_cutState {x : WordLangCutsetsHOL} {s t : WordSemStateFiniteExact width C F}
    (h : cutState x s = some t) : StackRel s t := by
  obtain ⟨_, rfl⟩ := cutStateConst _ _ _ h
  exact StackRel.refl _

theorem stackRel_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : StackRel s (alloc w names s).2 := by
  unfold alloc
  split
  · exact StackRel.refl _
  · rename_i envs _
    split
    · exact StackRel.refl _
    · rename_i g hg
      have hgc := gcConst _ _ hg
      have hpush : StackRel s g :=
        StackRel.trans (StackRel.refl _ : StackRel s (setStore .allocSize (.word w) s))
          (StackRel.trans (stackRel_pushEnv envs none _)
            (StackRel.of_eq hgc.2.2.2.2.2.2.2.2.2.2.1 hgc.2.2.2.2.2.2.2.2.2.2.2.1))
      split
      · exact hpush
      · rename_i p hp
        have hpop := StackRel.trans hpush (stackRel_popEnv hp)
        split
        · exact hpop
        · split
          · exact hpop
          · exact hpop
          · exact hpop

theorem stackRel_shareInst (op : WordMemOp) (v : Nat) (c : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    StackRel s (shareInst (rw := width) op v c s).2 := by
  have := shareInstConst op v c s _ _ rfl
  exact StackRel.of_eq this.2.2.2.2.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option linter.unusedSimpArgs false in
/-- Every statement that neither recurses nor reads the clock. -/
theorem stackRel_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) :
    StackRel s (evaluate p s).2 := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | exact StackRel.refl _
      | exact stackRel_alloc _ _ _
      | exact stackRel_shareInst _ _ _ _
      | (rename_i h; have := instConstFull _ _ _ h
         exact StackRel.of_eq this.2.2.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.2.2.1)
      | (rename_i h; have := memStoreConst _ _ _ _ h
         exact StackRel.of_eq this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
           this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      | (rename_i h; have := jumpExcConst _ _ _ h
         exact StackRel.of_eq this.2.2.2.2.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2.2.2.2.2.2.1)
      | exact ⟨rfl, by simp [optionLe]⟩
      | exact StackRel.of_eq rfl rfl
      | (dsimp only; split
         · exact ⟨rfl, by simp [optionLe]⟩
         · exact StackRel.refl _)

end Helpers

section Evaluate

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_stack_max_le` and `evaluate_stack_limit`,
    by recursion on HOL's termination measure.  The cases follow HOL's
    `evaluate_ind` clauses. -/
theorem stackRel_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      StackRel s (evaluate p s).2
  | .tick, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> exact StackRel.of_eq rfl rfl
  | .mustTerminate q, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]; exact StackRel.refl _
      · simp only [hz, dite_false, if_false]
        have ih := stackRel_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 }
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => exact ih
        | some x => cases x <;> first | exact StackRel.refl _ | exact ih
  | .seq c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      have ih1 := stackRel_evaluate c1 s
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none => exact ih1.trans (stackRel_evaluate c2 s1)
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
      all_goals try exact StackRel.refl _
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · exact StackRel.refl _
      · exact stackRel_evaluate c2 s
      · exact stackRel_evaluate c1 s
  | .loop names c exitNames, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact StackRel.refl _
      simp only
      have hcut := stackRel_cutState hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := stackRel_evaluate c s'
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      rw [hb] at ih
      have hc := evaluate_clock c s' rb s1 hb
      have hb1 := hcut.trans ih
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true]
          exact hb1.trans (StackRel.of_eq rfl rfl)
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          exact (hb1.trans (StackRel.of_eq rfl rfl)).trans
            (stackRel_evaluate (.loop names c exitNames) (decClock s1))
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact hb1
          · rename_i s2 hce
            exact hb1.trans (stackRel_cutState hce)
        · exact hb1
  | .call ret dest args handler, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · exact StackRel.refl _
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]; exact StackRel.refl _
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · exact StackRel.refl _
      simp only
      cases ret with
      | none =>
        cases handler with
        | some _ => exact StackRel.refl _
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true]; exact StackRel.of_eq rfl rfl
          simp only [hz, dite_false, if_false]
          have ih := stackRel_evaluate prog (callEnv args1 ss (decClock s))
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          have hpre : StackRel s (callEnv args1 ss (decClock s)) :=
            (StackRel.of_eq rfl rfl).trans (stackRel_callEnv _ _ _)
          simp only
          split
          · exact hpre.trans ih
          · exact hpre.trans ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]; exact StackRel.refl _
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact StackRel.refl _
        simp only
        by_cases hz : s.clock = 0
        · simp only [hz, dite_true, if_true]
          exact ⟨rfl, callPushEnv_optionLe_stackMax args1 ss envs handler s⟩
        simp only [hz, dite_false, if_false]
        have hpre : StackRel s (callEnv args1 ss (pushEnv envs handler (decClock s))) :=
          ((StackRel.of_eq rfl rfl : StackRel s (decClock s)).trans
            (stackRel_pushEnv envs handler _)).trans
            (stackRel_callEnv _ _ _)
        have ih := stackRel_evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih
        have hc := evaluate_clock prog _ rc s2 hcv
        have h2 := hpre.trans ih
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
        · exact h2
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]; exact h2
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · exact h2
          simp only
          have h3 := h2.trans (stackRel_popEnv hp)
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · exact (h3.trans (StackRel.of_eq rfl rfl)).trans
              (stackRel_evaluate retHandler (setVars n ys s1))
          · exact h3
        · cases handler with
          | none => exact h2
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only
            split
            · exact h2
            · split
              · exact (h2.trans (StackRel.of_eq rfl rfl)).trans
                  (stackRel_evaluate hprog (setVar n' y s2))
              · exact h2
        all_goals exact h2
  | .skip, s => stackRel_evaluate_const s _ rfl
  | .move a b, s => stackRel_evaluate_const s _ rfl
  | .inst a, s => stackRel_evaluate_const s _ rfl
  | .assign a b, s => stackRel_evaluate_const s _ rfl
  | .get a b, s => stackRel_evaluate_const s _ rfl
  | .set a b, s => stackRel_evaluate_const s _ rfl
  | .store a b, s => stackRel_evaluate_const s _ rfl
  | .alloc a b, s => stackRel_evaluate_const s _ rfl
  | .storeConsts a b c d f, s => stackRel_evaluate_const s _ rfl
  | .raise a, s => stackRel_evaluate_const s _ rfl
  | WordLangProgHOL.return a b, s => stackRel_evaluate_const s _ rfl
  | WordLangProgHOL.break a, s => stackRel_evaluate_const s _ rfl
  | WordLangProgHOL.continue a, s => stackRel_evaluate_const s _ rfl
  | .opCurrHeap a b c, s => stackRel_evaluate_const s _ rfl
  | .locValue a b, s => stackRel_evaluate_const s _ rfl
  | .install a b c d f, s => stackRel_evaluate_const s _ rfl
  | .codeBufferWrite a b, s => stackRel_evaluate_const s _ rfl
  | .dataBufferWrite a b, s => stackRel_evaluate_const s _ rfl
  | .ffi a b c d f g, s => stackRel_evaluate_const s _ rfl
  | .shareInst a b c, s => stackRel_evaluate_const s _ rfl
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

end Evaluate

/-- Exact HOL `evaluate_stack_max_le` (`wordPropsScript.sml:4312-4370`):
    `∀c s1 res s2. evaluate (c,s1) = (res,s2) ⇒ option_le s1.stack_max
    s2.stack_max`.  Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_max_le {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) → optionLe s1.stackMax s2.stackMax := by
  intro c s1 res s2 h
  have := (stackRel_evaluate c s1).2
  rwa [h] at this

/-- Exact HOL `evaluate_stack_max` (`wordPropsScript.sml:4372-4384`).  HOL's
    `the` is `miscThe` and `>=` on `num` is `≥` on `Nat`.  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_max {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) →
        match s1.stackMax with
        | none => s2.stackMax = none
        | some stackMax => miscThe stackMax s2.stackMax ≥ stackMax := by
  intro c s1 res s2 h
  have hle := evaluate_stack_max_le c s1 res s2 h
  rcases h1 : s1.stackMax with _ | m <;> rcases h2 : s2.stackMax with _ | m2 <;>
    simp_all [optionLe, miscThe]

/-- Exact HOL `evaluate_stack_max_IS_SOME` (`wordPropsScript.sml:4386-4393`).
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_max_IS_SOME {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) ∧ s2.stackMax.isSome = true → s1.stackMax.isSome = true := by
  intro c s1 res s2 ⟨h, hs⟩
  have := evaluate_stack_max c s1 res s2 h
  rcases h1 : s1.stackMax with _ | m
  · rw [h1] at this; simp [this] at hs
  · rfl

/-- Exact HOL `evaluate_stack_limit` (`wordPropsScript.sml:4395-4417`).
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_limit {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) → s2.stackLimit = s1.stackLimit := by
  intro c s1 res s2 h
  have := (stackRel_evaluate c s1).1
  rwa [h] at this

/-- Exact HOL `evaluate_stack_limit_stack_max_eq` (`wordPropsScript.sml:4419-4429`).
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_limit_stack_max_eq {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) ∧ miscThe s1.stackLimit s1.stackMax ≥ s1.stackLimit →
        miscThe s2.stackLimit s2.stackMax ≥ s2.stackLimit := by
  intro c s1 res s2 ⟨h, hge⟩
  have hm := evaluate_stack_max c s1 res s2 h
  have hl := evaluate_stack_limit c s1 res s2 h
  rw [hl]
  rcases h1 : s1.stackMax with _ | m <;> rcases h2 : s2.stackMax with _ | m2 <;>
    (simp_all [miscThe]; try omega)

/-- Exact HOL `evaluate_stack_limit_stack_max` (`wordPropsScript.sml:4431-4441`).
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_stack_limit_stack_max {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate c s1 = (res, s2) ∧ miscThe (s1.stackLimit + 1) s1.stackMax > s1.stackLimit →
        miscThe (s2.stackLimit + 1) s2.stackMax > s2.stackLimit := by
  intro c s1 res s2 ⟨h, hgt⟩
  have hm := evaluate_stack_max c s1 res s2 h
  have hl := evaluate_stack_limit c s1 res s2 h
  rw [hl]
  rcases h1 : s1.stackMax with _ | m <;> rcases h2 : s2.stackMax with _ | m2 <;>
    (simp_all [miscThe]; try omega)

end WordSemStateFiniteExact

end Flapjack
