import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax

/-!
# wordProps `evaluate_consts` evaluator constancy family

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1740-1759`
(bead `flapjack-pxn.18.5.15.3.27.1.1.4.4`), with the helper results its proof
uses: `pop_env_code_gc_fun_clock` (516), `alloc_code_gc_fun_const` (670) and
the local `inst_code_gc_fun_const` (924).  The evaluator theorem is over the
native exact `evaluate` with arbitrary programs, states, results and positive
word width.

HOL proves `evaluate_consts` by `recInduct evaluate_ind`.  Here it follows
from an untagged recursion on HOL's termination measure, as for
`evaluate_stack_max_le` in `EvaluateStackMax`, whose motive is the six-field
conjunction of the conclusion.  The primitive cases use the same helper facts
as HOL (`alloc_code_gc_fun_const`, `inst_code_gc_fun_const`, `mem_store_const`,
`jump_exc_const`, `share_inst_const`, `pop_env_code_gc_fun_clock`,
`cut_state_const`).

Inherited assumption: `evaluate`'s `Inst` clause and `inst_code_gc_fun_const`
reach the tagged `inst`, which carries `(reals_as_rational_cuts)` for its
`FPSqrt` rendering; those declarations record the inherited `docs/SOUNDNESS.md`
item 8 assumption in the theorem map.  No numerical floating-point claim is
made.
-/

namespace Flapjack

namespace WordSemEvaluateConstsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateConstsSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `pop_env_code_gc_fun_clock` (`wordPropsScript.sml:516-534`): all
    thirteen original equalities, oriented `r.f = x.f` as in HOL, from the sole
    successful `pop_env` premise. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "pop_env_code_gc_fun_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem popEnvCodeGcFunClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r x : WordSemStateFiniteExact width C F) (h : popEnv r = some x) :
    r.code = x.code ∧
    r.codeBuffer = x.codeBuffer ∧
    r.dataBuffer = x.dataBuffer ∧
    r.gcFun = x.gcFun ∧
    r.clock = x.clock ∧
    r.be = x.be ∧
    r.mdomain = x.mdomain ∧
    r.shMdomain = x.shMdomain ∧
    r.compile = x.compile ∧
    r.compileOracle = x.compileOracle ∧
    r.stackLimit = x.stackLimit ∧
    r.stackMax = x.stackMax ∧
    r.stackSize = x.stackSize := by
  unfold popEnv at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Option.some.injEq] at h; subst h; simp)

/-- Exact HOL `alloc_code_gc_fun_const` (`wordPropsScript.sml:670-688`): all
    eleven original field conclusions from the sole `alloc` equation, for an
    arbitrary allocation word, cutsets, result and states, covering every
    error, GC failure, pop failure, space and `NotEnoughSpace` branch. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "alloc_code_gc_fun_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocCodeGcFunConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : BitVec width) (names : WordLangCutsetsHOL)
    (s t : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (h : alloc x names s = (res, t)) :
    t.code = s.code ∧
    t.codeBuffer = s.codeBuffer ∧
    t.dataBuffer = s.dataBuffer ∧
    t.gcFun = s.gcFun ∧
    t.mdomain = s.mdomain ∧
    t.shMdomain = s.shMdomain ∧
    t.be = s.be ∧
    t.compile = s.compile ∧
    t.compileOracle = s.compileOracle ∧
    t.stackLimit = s.stackLimit ∧
    t.stackSize = s.stackSize := by
  unfold alloc at h
  split at h
  · cases h; simp [flushState]
  · rename_i envs _
    split at h
    · cases h; simp [flushState]
    · rename_i g hg
      have hgs : g = { pushEnv envs none (setStore .allocSize (.word x) s) with
          stack := g.stack, store := g.store, memory := g.memory } := by
        unfold gc at hg
        dsimp only at hg
        repeat' split at hg
        all_goals first
          | (simp only [reduceCtorEq] at hg)
          | (simp only [Option.some.injEq] at hg; subst hg; rfl)
      have hp : (pushEnv envs none (setStore .allocSize (.word x) s)).code = s.code ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).codeBuffer = s.codeBuffer ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).dataBuffer = s.dataBuffer ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).gcFun = s.gcFun ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).mdomain = s.mdomain ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).shMdomain = s.shMdomain ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).be = s.be ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).compile = s.compile ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).compileOracle =
            s.compileOracle ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).stackLimit = s.stackLimit ∧
          (pushEnv envs none (setStore .allocSize (.word x) s)).stackSize = s.stackSize :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hgs] at h
      generalize g.stack = gstack at h
      generalize g.store = gstore at h
      generalize g.memory = gmemory at h
      split at h
      · cases h; simp [flushState]; exact hp
      · rename_i p hpop
        have hq := popEnvCodeGcFunClock _ _ hpop
        rcases hq with ⟨q1, q2, q3, q4, _, q6, q7, q8, q9, q10, q11, _, q13⟩
        rcases hp with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩
        have fields : p.code = s.code ∧ p.codeBuffer = s.codeBuffer ∧
            p.dataBuffer = s.dataBuffer ∧ p.gcFun = s.gcFun ∧ p.mdomain = s.mdomain ∧
            p.shMdomain = s.shMdomain ∧ p.be = s.be ∧ p.compile = s.compile ∧
            p.compileOracle = s.compileOracle ∧ p.stackLimit = s.stackLimit ∧
            p.stackSize = s.stackSize :=
          ⟨q1.symm.trans p1, q2.symm.trans p2, q3.symm.trans p3, q4.symm.trans p4,
            q7.symm.trans p5, q8.symm.trans p6, q6.symm.trans p7, q9.symm.trans p8,
            q10.symm.trans p9, q11.symm.trans p10, q13.symm.trans p11⟩
        split at h
        · cases h; exact fields
        · split at h
          · cases h; exact fields
          · cases h; exact fields
          · cases h; simpa [flushState] using fields

/-- Exact HOL local `inst_code_gc_fun_const` (`wordPropsScript.sml:924-933`):
    the original eight equalities, oriented `s.f = t.f` as in HOL, for an
    arbitrary instruction and the sole successful `inst` premise. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_code_gc_fun_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instCodeGcFunConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (s t : WordSemStateFiniteExact width C F)
    (h : inst i s = some t) :
    s.code = t.code ∧ s.gcFun = t.gcFun ∧ s.shMdomain = t.shMdomain ∧ s.mdomain = t.mdomain ∧
    s.be = t.be ∧ s.compile = t.compile ∧ s.stackSize = t.stackSize ∧
    s.stackLimit = t.stackLimit := by
  unfold inst at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp [setVar, setFpVar])
    | (unfold assign at h; split at h
       · cases h
       · cases h; simp [setVar])
    | (rename_i heq; cases h
       unfold memStore at heq
       split at heq <;> cases heq; simp)

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The motive of the recursion: the six fields of HOL `evaluate_consts`. -/
def ConstRel (s t : WordSemStateFiniteExact width C F) : Prop :=
  s.gcFun = t.gcFun ∧ s.mdomain = t.mdomain ∧ s.shMdomain = t.shMdomain ∧ s.be = t.be ∧
    s.compile = t.compile ∧ s.stackLimit = t.stackLimit

theorem ConstRel.refl (s : WordSemStateFiniteExact width C F) : ConstRel s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ConstRel.trans {s t u : WordSemStateFiniteExact width C F}
    (h1 : ConstRel s t) (h2 : ConstRel t u) : ConstRel s u :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
    h1.2.2.2.1.trans h2.2.2.2.1, h1.2.2.2.2.1.trans h2.2.2.2.2.1,
    h1.2.2.2.2.2.trans h2.2.2.2.2.2⟩

theorem constRel_popEnv {s t : WordSemStateFiniteExact width C F} (h : popEnv s = some t) :
    ConstRel s t := by
  obtain ⟨_, _, _, h4, _, h6, h7, h8, h9, _, h11, _, _⟩ := popEnvCodeGcFunClock _ _ h
  exact ⟨h4, h7, h8, h6, h9, h11⟩

theorem constRel_cutState {x : WordLangCutsetsHOL} {s t : WordSemStateFiniteExact width C F}
    (h : cutState x s = some t) : ConstRel s t := by
  obtain ⟨_, rfl⟩ := cutStateConst _ _ _ h
  exact ConstRel.refl _

theorem constRel_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : ConstRel s (alloc w names s).2 := by
  have := allocCodeGcFunConst w names s (alloc w names s).2 (alloc w names s).1 rfl
  exact ⟨this.2.2.2.1.symm, this.2.2.2.2.1.symm, this.2.2.2.2.2.1.symm,
    this.2.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.2.1.symm,
    this.2.2.2.2.2.2.2.2.2.1.symm⟩

theorem constRel_shareInst (op : WordMemOp) (v : Nat) (c : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    ConstRel s (shareInst (rw := width) op v c s).2 := by
  have := shareInstConst op v c s _ _ rfl
  exact ⟨this.2.1.symm, this.2.2.1.symm, this.2.2.2.1.symm, this.1.symm,
    this.2.2.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.2.2.2.2.2.2.1.symm⟩

set_option linter.unusedSimpArgs false in
/-- Every statement that neither recurses nor reads the clock. -/
theorem constRel_evaluate_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) :
    ConstRel s (evaluate p s).2 := by
  cases p <;> simp only [wordProgClockConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | exact ConstRel.refl _
      | exact constRel_alloc _ _ _
      | exact constRel_shareInst _ _ _ _
      | (rename_i h; have := instCodeGcFunConst _ _ _ h
         exact ⟨this.2.1, this.2.2.2.1, this.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
           this.2.2.2.2.2.2.2⟩)
      | (rename_i h; have := memStoreConst _ _ _ _ h
         exact ⟨this.2.2.2.1.symm, this.2.2.2.2.1.symm, this.2.2.2.2.2.1.symm,
           this.2.2.1.symm, this.2.2.2.2.2.2.2.2.2.2.2.1.symm,
           this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm⟩)
      | (rename_i h; have := jumpExcConst _ _ _ h
         exact ⟨this.2.1.symm, this.2.2.1.symm, this.2.2.2.1.symm, this.1.symm,
           this.2.2.2.2.2.2.2.1.symm, this.2.2.2.2.2.2.2.2.2.2.2.1.symm⟩)
      | (dsimp only; split
         · exact ConstRel.refl _
         · exact ConstRel.refl _)

end Helpers


section Evaluate

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_consts`,
    by recursion on HOL's termination measure.  The cases follow HOL's
    `evaluate_ind` clauses. -/
theorem constRel_evaluate :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      ConstRel s (evaluate p s).2
  | .tick, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | .mustTerminate q, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]; exact ConstRel.refl _
      · simp only [hz, dite_false, if_false]
        have ih := constRel_evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 }
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        cases r with
        | none => exact ih
        | some x => cases x <;> first | exact ConstRel.refl _ | exact ih
  | .seq c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      have ih1 := constRel_evaluate c1 s
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none => exact ih1.trans (constRel_evaluate c2 s1)
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
      all_goals try exact ConstRel.refl _
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · exact ConstRel.refl _
      · exact constRel_evaluate c2 s
      · exact constRel_evaluate c1 s
  | .loop names c exitNames, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact ConstRel.refl _
      simp only
      have hcut := constRel_cutState hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := constRel_evaluate c s'
      rcases hb : evaluate c s' with ⟨rb, s1⟩
      rw [hb] at ih
      have hc := evaluate_clock c s' rb s1 hb
      have hb1 := hcut.trans ih
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true]
          exact hb1.trans (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          exact (hb1.trans (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans
            (constRel_evaluate (.loop names c exitNames) (decClock s1))
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · split
          · exact hb1
          · rename_i s2 hce
            exact hb1.trans (constRel_cutState hce)
        · exact hb1
  | .call ret dest args handler, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · exact ConstRel.refl _
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]; exact ConstRel.refl _
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · exact ConstRel.refl _
      simp only
      cases ret with
      | none =>
        cases handler with
        | some _ => exact ConstRel.refl _
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [hz, dite_false, if_false]
          have ih := constRel_evaluate prog (callEnv args1 ss (decClock s))
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          have hpre : ConstRel s (callEnv args1 ss (decClock s)) :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only
          split
          · exact hpre.trans ih
          · exact hpre.trans ih
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]; exact ConstRel.refl _
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact ConstRel.refl _
        simp only
        by_cases hz : s.clock = 0
        · simp only [hz, dite_true, if_true]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        simp only [hz, dite_false, if_false]
        have hpre : ConstRel s (callEnv args1 ss (pushEnv envs handler (decClock s))) :=
          by rcases handler with _ | ⟨_, _, _, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        have ih := constRel_evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))
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
          have h3 := h2.trans (constRel_popEnv hp)
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          split
          · exact (h3.trans (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans
              (constRel_evaluate retHandler (setVars n ys s1))
          · exact h3
        · cases handler with
          | none => exact h2
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only
            split
            · exact h2
            · split
              · exact (h2.trans (⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans
                  (constRel_evaluate hprog (setVar n' y s2))
              · exact h2
        all_goals exact h2
  | .skip, s => constRel_evaluate_const s _ rfl
  | .move a b, s => constRel_evaluate_const s _ rfl
  | .inst a, s => constRel_evaluate_const s _ rfl
  | .assign a b, s => constRel_evaluate_const s _ rfl
  | .get a b, s => constRel_evaluate_const s _ rfl
  | .set a b, s => constRel_evaluate_const s _ rfl
  | .store a b, s => constRel_evaluate_const s _ rfl
  | .alloc a b, s => constRel_evaluate_const s _ rfl
  | .storeConsts a b c d f, s => constRel_evaluate_const s _ rfl
  | .raise a, s => constRel_evaluate_const s _ rfl
  | WordLangProgHOL.return a b, s => constRel_evaluate_const s _ rfl
  | WordLangProgHOL.break a, s => constRel_evaluate_const s _ rfl
  | WordLangProgHOL.continue a, s => constRel_evaluate_const s _ rfl
  | .opCurrHeap a b c, s => constRel_evaluate_const s _ rfl
  | .locValue a b, s => constRel_evaluate_const s _ rfl
  | .install a b c d f, s => constRel_evaluate_const s _ rfl
  | .codeBufferWrite a b, s => constRel_evaluate_const s _ rfl
  | .dataBufferWrite a b, s => constRel_evaluate_const s _ rfl
  | .ffi a b c d f g, s => constRel_evaluate_const s _ rfl
  | .shareInst a b c, s => constRel_evaluate_const s _ rfl
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

/-- Exact HOL `evaluate_consts` (`wordPropsScript.sml:1740-1759`): for an
    arbitrary program, state, result and post-state, the sole premise
    `evaluate (xs,s1) = (vs,s2)` gives the six original equalities in source
    order and orientation.  Inherits `reals_as_rational_cuts` through
    `evaluate`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_consts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_consts {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (xs : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (vs : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate xs s1 = (vs, s2) →
        s1.gcFun = s2.gcFun ∧ s1.mdomain = s2.mdomain ∧ s1.shMdomain = s2.shMdomain ∧
          s1.be = s2.be ∧ s1.compile = s2.compile ∧ s1.stackLimit = s2.stackLimit := by
  intro xs s1 vs s2 h
  have := constRel_evaluate xs s1
  rw [h] at this
  exact this

end WordSemStateFiniteExact

end Flapjack
