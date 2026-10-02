import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

/-! StackProps `evaluate_consts` (`stackPropsScript.sml:400-418`) over the tagged exact StackSem
`evaluate` (`EvaluateDef.lean`). HOL proves it by `recInduct evaluate_ind` with the
`alloc_const`, `inst_const`, `store_const_sem_const` and `sh_mem_op_const` lemmas; here the
induction is the clock-first lexicographic measure that defines `evaluate`, as for
`evaluate_add_clock`, with every clause unfolded by its `evaluate_def` equation. -/

namespace Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemMeasure
open Flapjack.StackSemEvaluate

namespace EvaluateConsts

/-- Canonical imported state codec witness; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- The eight fields `evaluate_consts` preserves (Flapjack infrastructure). -/
def Consts {width : Nat} [NeZero width] {C F : Type}
    (s t : StackSemStateFiniteExact width C F) : Prop :=
  t.useAlloc = s.useAlloc ∧ t.useStore = s.useStore ∧ t.useStack = s.useStack ∧
    t.be = s.be ∧ t.gcFun = s.gcFun ∧ t.mdomain = s.mdomain ∧ t.shMdomain = s.shMdomain ∧
    t.compile = s.compile

theorem Consts.trans {width : Nat} [NeZero width] {C F : Type}
    {s t u : StackSemStateFiniteExact width C F} (h1 : Consts s t) (h2 : Consts t u) :
    Consts s u := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, k1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, k2⟩ := h2
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    g2.trans g1, k2.trans k1⟩

theorem consts_of_eq {width : Nat} [NeZero width] {C F : Type}
    {s t : StackSemStateFiniteExact width C F}
    (ha : t.useAlloc = s.useAlloc) (hb : t.useStore = s.useStore) (hc : t.useStack = s.useStack)
    (hd : t.be = s.be) (he : t.gcFun = s.gcFun) (hf : t.mdomain = s.mdomain)
    (hg : t.shMdomain = s.shMdomain) (hk : t.compile = s.compile) : Consts s t :=
  ⟨ha, hb, hc, hd, he, hf, hg, hk⟩

/-- Leaf clauses: the returned state agrees with the input on every preserved field. -/
local macro "leaf_consts" h:ident : tactic =>
  `(tactic| (
    repeat' (first | (simp only [Prod.mk.injEq] at $h:ident; obtain ⟨-, h2⟩ := $h; subst h2) | split at $h:ident | dsimp only at $h:ident)
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | skip))

/-- The induction on HOL's `evaluate` measure, carrying the source statement. -/
theorem consts_measure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (m : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = m → ∀ (r : Option (StackSemResult width))
        (s' : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, s') → Consts s s' := by
  intro m
  induction m using EvaluateAddClock.lexNat_wf.induction with
  | _ m ih =>
  intro p s hm r s' h
  subst hm
  have ihc : ∀ (q : HolProg width) (t : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q t) (stackSemMeasure p s) → Consts t (evaluate (q, t)).2 :=
    fun q t hlt => ih _ hlt q t rfl _ _ rfl
  cases p
  case skip => rw [evaluate_skip] at h; leaf_consts h
  case halt v => rw [evaluate_halt] at h; leaf_consts h
  case ret v => rw [evaluate_ret] at h; leaf_consts h
  case raise v => rw [evaluate_raise] at h; leaf_consts h
  case «break» v => rw [evaluate_break] at h; leaf_consts h
  case «continue» v => rw [evaluate_continue] at h; leaf_consts h
  case get v n => rw [evaluate_get] at h; leaf_consts h
  case set n v => rw [evaluate_set] at h; leaf_consts h
  case opCurrHeap b d src => rw [evaluate_opCurrHeap] at h; leaf_consts h
  case tick => rw [evaluate_tick] at h; leaf_consts h
  case install a b c d e => rw [evaluate_install] at h; leaf_consts h
  case codeBufferWrite a b => rw [evaluate_codeBufferWrite] at h; leaf_consts h
  case dataBufferWrite a b => rw [evaluate_dataBufferWrite] at h; leaf_consts h
  case ffi n a b c d e => rw [evaluate_ffi] at h; leaf_consts h
  case locValue a b c => rw [evaluate_locValue] at h; leaf_consts h
  case stackAlloc n => rw [evaluate_stackAlloc] at h; leaf_consts h
  case stackFree n => rw [evaluate_stackFree] at h; leaf_consts h
  case stackLoad a b => rw [evaluate_stackLoad] at h; leaf_consts h
  case stackLoadAny a b => rw [evaluate_stackLoadAny] at h; leaf_consts h
  case stackStore a b => rw [evaluate_stackStore] at h; leaf_consts h
  case stackStoreAny a b => rw [evaluate_stackStoreAny] at h; leaf_consts h
  case stackGetSize a => rw [evaluate_stackGetSize] at h; leaf_consts h
  case stackSetSize a => rw [evaluate_stackSetSize] at h; leaf_consts h
  case bitmapLoad a b => rw [evaluate_bitmapLoad] at h; leaf_consts h
  case inst i =>
    rw [evaluate_inst] at h
    split at h
    · rename_i t ht
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      obtain ⟨-, -, a, b, c, -, d, e, f, g, -, k, -⟩ :=
        StackPropsInstructionConstants.instConst _ s t ht
      exact ⟨a, b, c, d, e, f, g, k⟩
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  case alloc n =>
    rw [evaluate_alloc] at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at h
      · rename_i w _
        obtain ⟨-, -, a, b, c, -, d, e, f, g, -, k, -⟩ :=
          StackPropsAllocationConstants.allocConst w s s' r h
        exact ⟨a, b, c, d, e, f, g, k⟩
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  case storeConsts t1 t2 stub =>
    rw [evaluate_storeConsts] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h))
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | (obtain ⟨-, -, a, b, c, -, d, e, f, g, -, k, -⟩ :=
          StackPropsAllocationConstants.storeConstSemConst _ _ s s' r h
         exact ⟨a, b, c, d, e, f, g, k⟩)
  case shMemOp op reg addr =>
    cases addr with
    | addr a w =>
    rw [evaluate_shMemOp] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h))
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | (obtain ⟨-, a1, b1, c1, -, d1, e1, f1, g1, -, k1, -⟩ :=
          StackPropsSharedMemoryClock.shMemOpConst _ _ _ _ s' r h
         exact ⟨a1, b1, c1, d1, e1, f1, g1, k1⟩)
  case seq c1 c2 =>
    rw [evaluate_seq] at h
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    have hc1 : Consts s t1 := by
      have := ihc c1 s (seq_first_measure_lt c1 c2 s); rw [h1] at this; exact this
    rw [h1] at h
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h
    cases r1 with
    | none =>
        have hlt := seq_second_measure_lt c1 c2 s ((none : Option (StackSemResult width)), t1)
        rw [hfx] at hlt
        exact Consts.trans hc1 (ih _ hlt c2 _ rfl r s' h)
    | some x =>
        simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hc1
  case ite cmp r1 ri c1 c2 =>
    rw [evaluate_ite] at h
    repeat' (first | (simp only [Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2) | split at h)
    all_goals first
      | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | exact ih _ (if_first_measure_lt cmp r1 ri c1 c2 s) c1 s rfl r s' h
      | exact ih _ (if_second_measure_lt cmp r1 ri c1 c2 s) c2 s rfl r s' h
  case loop c1 =>
    rw [evaluate_loop] at h
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    have hc1 : Consts s t1 := by
      have := ihc c1 s (loop_body_measure_lt c1 s); rw [h1] at this; exact this
    rw [h1] at h
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h
    dsimp only at h
    split at h
    · split at h
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hc1
      · rename_i h0
        have hlt := loop_reentry_measure_lt c1 s (r1, t1) (by rw [hfx]; exact h0)
        rw [hfx] at hlt
        exact Consts.trans hc1 (ih _ hlt (.loop c1) _ rfl r s' h)
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hc1
  case jumpLower r1 r2 dest =>
    rw [evaluate_jumpLower] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → Consts s t → Consts s s' := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    split at h
    · split at h
      · split at h
        · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rename_i prog _
          split at h
          · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rename_i h0
            rcases h1 : evaluate (prog, decClock s) with ⟨res1, t1⟩
            rw [h1] at h
            have hc : Consts s t1 :=
              ih _ (callee_measure_lt prog _ s h0) prog _ rfl res1 t1 h1
            dsimp only at h
            split at h
            · exact leaf _ _ h hc
            · exact leaf _ _ h hc
      · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  case rawCall dest =>
    rw [evaluate_rawCall] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → Consts s t → Consts s s' := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    split at h
    · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split at h
      · rename_i body _
        split at h
        · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rename_i h0
          rcases h1 : evaluate (body, decClock s) with ⟨r1, t1⟩
          rw [h1] at h
          have hc : Consts s t1 :=
            ih _ (callee_measure_lt body _ s h0) body _ rfl r1 t1 h1
          dsimp only at h
          split at h
          · exact leaf _ _ h hc
          · exact leaf _ _ h hc
      · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  case call ret dest handler =>
    rw [evaluate_call] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → Consts s t → Consts s s' := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    cases ret with
    | none =>
      dsimp only at h
      split at h
      · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i prog _
        split at h
        · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · split at h
          · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rename_i h0
            rcases h1 : evaluate (prog, decClock s) with ⟨r1, t1⟩
            rw [h1] at h
            have hc : Consts s t1 :=
              ih _ (callee_measure_lt prog _ s h0) prog _ rfl r1 t1 h1
            simp only [fixClock] at h
            by_cases hb : StackSemControl.badFunReturn r1 = true
            · simp only [hb, if_true] at h; exact leaf _ _ h hc
            · simp only [hb, Bool.false_eq_true, if_false] at h; exact leaf _ _ h hc
    | some rr =>
      obtain ⟨retH, link, l1, l2⟩ := rr
      dsimp only at h
      split at h
      · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rename_i prog _
        split at h
        · exact leaf _ _ h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rename_i h0
          have h0' : (setVar link (.loc l1 l2) s).clock ≠ 0 := h0
          rcases h1 : evaluate (prog, decClock (setVar link (.loc l1 l2) s)) with ⟨r1, t1⟩
          rw [h1] at h
          have hc : Consts s t1 :=
            ih _ (lexNat_decClock (setVar link (.loc l1 l2) s) _ _ h0') prog _ rfl r1 t1 h1
          have hfx : fixClock (decClock (setVar link (.loc l1 l2) s)) (r1, t1) =
              (r1, { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock }) :=
            rfl
          have hlt := fun cont => call_continuation_measure_lt cont
            (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2 (r1, t1) h0
          rw [hfx] at h hlt
          try dsimp only at h
          rcases r1 with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
          all_goals try (exact leaf _ _ h hc)
          · by_cases hx : x = .loc l1 l2
            · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
              exact Consts.trans hc (ih _ (hlt retH) retH _ rfl r s' h)
            · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
              exact leaf _ _ h hc
          · rcases handler with _ | ⟨hp, hl1, hl2⟩
            · exact leaf _ _ h hc
            · by_cases hx : x = .loc hl1 hl2
              · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
                exact Consts.trans hc (ih _ (hlt hp) hp _ rfl r s' h)
              · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
                exact leaf _ _ h hc

end EvaluateConsts

open EvaluateConsts in
/-- Exact HOL `evaluate_consts` (`stackPropsScript.sml:400-418`): an evaluation preserves
`use_alloc`, `use_store`, `use_stack`, `be`, `gc_fun`, `mdomain`, `sh_mdomain` and `compile`. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_consts"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateConsts {width : Nat} [NeZero width] {C F : Type} :
    ∀ (c : HolProg width) (s : StackSemStateFiniteExact width C F)
      (r : Option (StackSemResult width)) (s1 : StackSemStateFiniteExact width C F),
      evaluate (c, s) = (r, s1) →
      s1.useAlloc = s.useAlloc ∧ s1.useStore = s.useStore ∧ s1.useStack = s.useStack ∧
        s1.be = s.be ∧ s1.gcFun = s.gcFun ∧ s1.mdomain = s.mdomain ∧
        s1.shMdomain = s.shMdomain ∧ s1.compile = s.compile :=
  fun c s r s1 h => consts_measure _ c s rfl r s1 h

end Flapjack.Compiler.Backend.StackProps
