import Mathlib.Tactic.Convert
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.StackProps.ClockSupport
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.AllocationConstants
import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock
import Flapjack.Compiler.Backend.StackProps.ExpressionClock

/-! StackProps `evaluate_add_clock` (`stackPropsScript.sml:495-534`) over the
tagged exact StackSem `evaluate` (`EvaluateDef.lean`).

HOL proves it by `recInduct evaluate_ind`; here the induction is the same
clock-first lexicographic measure that defines `evaluate` (`stackSemMeasure`),
and every clause is unfolded by its `evaluate_def` equation. The clock-free
clauses use the source `*_with_const`/`*_const` lemmas (`inst`, `alloc`,
`store_const_sem`, `sh_mem_op`, `word_exp`). -/

namespace Flapjack.Compiler.Backend.StackProps

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemMeasure
open Flapjack.StackSemEvaluate

namespace EvaluateAddClock

/-- Canonical imported state codec witness; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Clamping commutes with adding the same clock to both states. -/
theorem fixClock_addClock {width : Nat} [NeZero width] {C F R : Type}
    (s t : StackSemStateFiniteExact width C F) (r : R) (extra : Nat) :
    fixClock { s with clock := s.clock + extra } (r, { t with clock := t.clock + extra }) =
      ((fixClock s (r, t)).1,
        { (fixClock s (r, t)).2 with clock := (fixClock s (r, t)).2.clock + extra }) := by
  simp only [fixClock, Prod.mk.injEq, true_and]
  congr 1
  omega

/-- Decrementing a nonzero clock commutes with adding to it. -/
theorem decClock_addClock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (extra : Nat) (h : s.clock ≠ 0) :
    decClock { s with clock := s.clock + extra } =
      { decClock s with clock := (decClock s).clock + extra } := by
  simp only [decClock]
  congr 1
  omega

/-- The clock-free clause shape: setting the input clock sets the output clock,
and the output clock is the input clock. -/
def ClockFree {width : Nat} [NeZero width] {C F : Type} (p : HolProg width) : Prop :=
  ∀ (s : StackSemStateFiniteExact width C F) (k : Nat),
    evaluate (p, { s with clock := k }) =
      ((evaluate (p, s)).1, { (evaluate (p, s)).2 with clock := k }) ∧
    (evaluate (p, s)).2.clock = s.clock

theorem addClock_of_clockFree {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} (hp : ClockFree (C := C) (F := F) p)
    (s s' : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (extra : Nat) (h : evaluate (p, s) = (r, s')) :
    evaluate (p, { s with clock := s.clock + extra }) =
      (r, { s' with clock := s'.clock + extra }) := by
  obtain ⟨h1, h2⟩ := hp s (s.clock + extra)
  rw [h1, h]
  rw [h] at h2
  simp only at h2
  rw [h2]

/-- Constructors whose clause neither reads the clock nor recurses. -/
def clockFreeCtor {width : Nat} [NeZero width] : HolProg width → Bool
  | .tick | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .jumpLower _ _ _ | .rawCall _
  | .call _ _ _ | .shMemOp _ _ _ | .inst _ | .alloc _ | .storeConsts _ _ _ => false
  | _ => true

theorem clockFree_of_ctor {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (hp : clockFreeCtor p = true) :
    ClockFree (C := C) (F := F) p := by
  intro s k
  cases p <;> simp only [clockFreeCtor, Bool.false_eq_true] at hp <;>
    simp only [evaluate_skip, evaluate_halt, evaluate_get, evaluate_set, evaluate_opCurrHeap,
      evaluate_ret, evaluate_raise, evaluate_break, evaluate_continue, evaluate_install,
      evaluate_codeBufferWrite, evaluate_dataBufferWrite, evaluate_ffi, evaluate_locValue,
      evaluate_stackAlloc, evaluate_stackFree, evaluate_stackLoad, evaluate_stackLoadAny,
      evaluate_stackStore, evaluate_stackStoreAny, evaluate_stackGetSize, evaluate_stackSetSize,
      evaluate_bitmapLoad, getVar, emptyEnv, setVar, setStore,
      StackPropsExpressionClock.wordExpWithClock, and_self] <;>
    repeat' (split <;> try simp_all)

/-- `Inst`, by `inst_with_const` and `inst_const`. -/
theorem clockFree_inst {width : Nat} [NeZero width] {C F : Type} (i : HolInst width) :
    ClockFree (C := C) (F := F) (.inst i : HolProg width) := by
  intro s k
  simp only [evaluate_inst, StackPropsInstructionConstants.instWithClock]
  cases h : StackSemInst.instHOL i s with
  | none => simp
  | some t => simp [(StackPropsInstructionConstants.instConst i s t h).2.1]

/-- `Alloc`, by `alloc_with_const` and `alloc_const`. -/
theorem clockFree_alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat) :
    ClockFree (C := C) (F := F) (.alloc n : HolProg width) := by
  intro s k
  simp only [evaluate_alloc, getVar]
  split
  · simp_all
  · split
    · rename_i w _
      rw [StackPropsAllocationConstants.allocWithClock]
      rcases h : StackSemAllocation.alloc w s with ⟨r, t⟩
      simp [(StackPropsAllocationConstants.allocConst w s t r h).2.1]
    · simp_all

/-- `StoreConsts`, by `store_const_sem_with_const` and `store_const_sem_const`. -/
theorem clockFree_storeConsts {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (stub : Option Nat) :
    ClockFree (C := C) (F := F) (.storeConsts t1 t2 stub : HolProg width) := by
  intro s k
  simp only [evaluate_storeConsts]
  split
  · simp_all
  · split
    · simp_all
    · split
      · simp_all
      · rw [StackPropsAllocationConstants.storeConstSemWithClock]
        rcases h : StackSemStoreConsts.storeConstSem t1 t2 s with ⟨r, t⟩
        simp [(StackPropsAllocationConstants.storeConstSemConst t1 t2 s t r h).2.1]

/-- HOL's termination order is well founded. -/
theorem lexNat_wf : WellFounded LexNat :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- The induction on HOL's `evaluate` measure, carrying the source statement. -/
theorem addClock_measure {width : Nat} [NeZero width] {C F : Type} (extra : Nat) :
    ∀ (m : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = m → ∀ (r : Option (StackSemResult width))
        (s' : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, s') → r ≠ some .timeOut →
      evaluate (p, { s with clock := s.clock + extra }) =
        (r, { s' with clock := s'.clock + extra }) := by
  intro m
  induction m using lexNat_wf.induction with
  | _ m ih =>
  intro p s hm r s' h hr
  subst hm
  have gv : ∀ v, getVar v { s with clock := s.clock + extra } = getVar v s := fun _ => rfl
  cases p
  all_goals first
    | exact addClock_of_clockFree (clockFree_of_ctor _ rfl) s s' r extra h
    | skip
  case inst i => exact addClock_of_clockFree (clockFree_inst i) s s' r extra h
  case alloc n => exact addClock_of_clockFree (clockFree_alloc n) s s' r extra h
  case storeConsts t1 t2 stub =>
    exact addClock_of_clockFree (clockFree_storeConsts t1 t2 stub) s s' r extra h
  case tick =>
    rw [evaluate_tick] at h ⊢
    by_cases h0 : s.clock = 0
    · simp only [h0, if_true, Prod.mk.injEq] at h
      exact absurd h.1.symm hr
    · simp only [h0, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_neg (show s.clock + extra ≠ 0 by omega), decClock_addClock s extra h0]
  case shMemOp op reg addr =>
    cases addr with
    | addr a w =>
    rw [evaluate_shMemOp] at h ⊢
    rw [StackPropsExpressionClock.wordExpWithClock]
    rcases hw : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with _ | a'
    · simp only [hw, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp only [hw] at h ⊢
      by_cases h0 : s.clock = 0
      · simp only [h0, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · simp only [h0, if_false] at h
        rw [if_neg (show s.clock + extra ≠ 0 by omega), decClock_addClock s extra h0,
          StackPropsSharedMemoryClock.shMemOpWithClock, h]
        have hc := (StackPropsSharedMemoryClock.shMemOpConst op reg a' (decClock s) s' r h).1
        simp [hc]
  case seq c1 c2 =>
    rw [evaluate_seq] at h ⊢
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    rw [h1] at h
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h
    have hne1 : r1 ≠ some .timeOut := by
      rintro rfl
      simp only [Prod.mk.injEq] at h
      exact hr h.1.symm
    rw [ih _ (seq_first_measure_lt c1 c2 s) c1 s rfl r1 t1 h1 hne1, fixClock_addClock, hfx]
    cases r1 with
    | none =>
      have hlt := seq_second_measure_lt c1 c2 s ((none : Option (StackSemResult width)), t1)
      rw [hfx] at hlt
      exact ih _ hlt c2 _ rfl r s' h hr
    | some x =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  case ite cmp r1 ri c1 c2 =>
    rw [evaluate_ite] at h ⊢
    have gvi : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri)
        { s with clock := s.clock + extra } =
        StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s := by
      cases HolRegImm.toWordRegImm ri <;> rfl
    rw [gv, gvi]
    rcases hx : getVar r1 s with _ | x <;>
      rcases hy : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with _ | y <;>
      simp only [hx, hy, Prod.mk.injEq] at h ⊢
    all_goals try (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hc, Prod.mk.injEq] at h ⊢
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · exact ih _ (if_second_measure_lt cmp r1 ri c1 c2 s) c2 s rfl r s' h hr
    · exact ih _ (if_first_measure_lt cmp r1 ri c1 c2 s) c1 s rfl r s' h hr
  case loop c1 =>
    rw [evaluate_loop] at h ⊢
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    rw [h1] at h
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    rw [hfx] at h
    have hne1 : r1 ≠ some .timeOut := by
      rintro rfl
      simp only [contLoop, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      exact hr h.1.symm
    rw [ih _ (loop_body_measure_lt c1 s) c1 s rfl r1 t1 h1 hne1, fixClock_addClock, hfx]
    by_cases hc : contLoop r1 = true
    · simp only [hc, if_true] at h ⊢
      by_cases h0 : min s.clock t1.clock = 0
      · simp only [h0, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · simp only [h0, if_false] at h
        rw [if_neg (show min s.clock t1.clock + extra ≠ 0 by omega)]
        have hlt := loop_reentry_measure_lt c1 s (r1, t1) (by rw [hfx]; exact h0)
        rw [hfx] at hlt
        have := ih _ hlt (.loop c1) _ rfl r s' h hr
        convert this using 3
        simp only [decClock]
        congr 1
        omega
    · simp only [hc, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  case jumpLower r1 r2 dest =>
    rw [evaluate_jumpLower] at h ⊢
    rw [gv, gv]
    rcases hx : getVar r1 s with _ | ⟨x⟩ | ⟨l1, l2⟩ <;>
      rcases hy : getVar r2 s with _ | ⟨y⟩ | ⟨m1, m2⟩ <;>
      simp only [hx, hy, Prod.mk.injEq] at h ⊢
    all_goals try (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    by_cases hl : wordCmpHOL .lower x y = true
    · simp only [hl, if_true] at h ⊢
      rcases hf : findCode (.inl dest) s.regs s.code with _ | prog <;>
        simp only [hf, Prod.mk.injEq] at h ⊢
      · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      by_cases h0 : s.clock = 0
      · simp only [h0, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      simp only [h0, if_false] at h
      rw [if_neg (show s.clock + extra ≠ 0 by omega), decClock_addClock s extra h0]
      rcases h1 : evaluate (prog, decClock s) with ⟨r1, t1⟩
      rw [h1] at h
      have hne1 : r1 ≠ some .timeOut := by
        rintro rfl
        simp only [badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
        exact hr h.1.symm
      rw [ih _ (callee_measure_lt prog _ s h0) prog _ rfl r1 t1 h1 hne1]
      by_cases hb : badFunReturn r1 = true
      · simp only [hb, if_true, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      · simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · simp only [hl, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case rawCall dest =>
    rw [evaluate_rawCall] at h ⊢
    rcases hf : sptLookup dest s.code with _ | prog <;> simp only [hf, Prod.mk.injEq] at h ⊢
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    rcases hd : destSeq prog with _ | ⟨_, body⟩ <;> simp only [hd, Prod.mk.injEq] at h ⊢
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    by_cases h0 : s.clock = 0
    · simp only [h0, if_true, Prod.mk.injEq] at h
      exact absurd h.1.symm hr
    simp only [h0, if_false] at h
    rw [if_neg (show s.clock + extra ≠ 0 by omega), decClock_addClock s extra h0]
    rcases h1 : evaluate (body, decClock s) with ⟨r1, t1⟩
    rw [h1] at h
    have hne1 : r1 ≠ some .timeOut := by
      rintro rfl
      simp only [badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      exact hr h.1.symm
    rw [ih _ (callee_measure_lt body _ s h0) body _ rfl r1 t1 h1 hne1]
    by_cases hb : badFunReturn r1 = true
    · simp only [hb, if_true, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  case call ret dest handler =>
    rw [evaluate_call] at h ⊢
    cases ret with
    | none =>
      simp only at h ⊢
      rcases hf : findCode dest s.regs s.code with _ | prog <;> simp only [hf, Prod.mk.injEq] at h ⊢
      · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      rcases handler with _ | hd <;> simp only [Prod.mk.injEq] at h ⊢
      · by_cases h0 : s.clock = 0
        · simp only [h0, if_true, Prod.mk.injEq] at h
          exact absurd h.1.symm hr
        simp only [h0, if_false] at h
        rw [if_neg (show s.clock + extra ≠ 0 by omega), decClock_addClock s extra h0]
        rcases h1 : evaluate (prog, decClock s) with ⟨r1, t1⟩
        rw [h1] at h
        have hne1 : r1 ≠ some .timeOut := by
          rintro rfl
          simp only [fixClock, badFunReturn, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
          exact hr h.1.symm
        rw [ih _ (callee_measure_lt prog _ s h0) prog _ rfl r1 t1 h1 hne1, fixClock_addClock]
        simp only [fixClock] at h ⊢
        by_cases hb : badFunReturn r1 = true
        · simp only [hb, if_true, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
        · simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | some rr =>
      obtain ⟨retH, link, l1, l2⟩ := rr
      simp only at h ⊢
      rcases hf : findCode dest (s.regs.eraseEq link) s.code with _ | prog <;>
        simp only [hf, Prod.mk.injEq] at h ⊢
      · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      by_cases h0 : s.clock = 0
      · simp only [h0, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      simp only [h0, if_false] at h
      rw [if_neg (show s.clock + extra ≠ 0 by omega)]
      have h0' : (setVar link (.loc l1 l2) s).clock ≠ 0 := h0
      have hsv : setVar link (.loc l1 l2) { s with clock := s.clock + extra } =
          { setVar link (.loc l1 l2) s with
            clock := (setVar link (.loc l1 l2) s).clock + extra } := rfl
      rw [hsv, decClock_addClock _ extra h0']
      rcases h1 : evaluate (prog, decClock (setVar link (.loc l1 l2) s)) with ⟨r1, t1⟩
      rw [h1] at h
      have hne1 : r1 ≠ some .timeOut := by
        rintro rfl
        simp only [fixClock, Prod.mk.injEq] at h
        exact hr h.1.symm
      rw [ih _ (lexNat_decClock (setVar link (.loc l1 l2) s) _ _ h0') prog _ rfl r1 t1 h1 hne1,
        fixClock_addClock]
      have hfx : fixClock (decClock (setVar link (.loc l1 l2) s)) (r1, t1) =
          (r1, { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock }) :=
        rfl
      have hlt := fun cont => call_continuation_measure_lt cont
        (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2 (r1, t1) h0
      rw [hfx] at h hlt
      rw [hfx]
      simp only at h ⊢
      rcases r1 with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
      all_goals try (simp only [Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      · by_cases hx : x = .loc l1 l2
        · simp only [hx, ne_eq, not_true_eq_false, if_false] at h ⊢
          exact ih _ (hlt retH) retH _ rfl r s' h hr
        · simp only [hx, ne_eq, not_false_eq_true, if_true, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
      · rcases handler with _ | ⟨hp, hl1, hl2⟩
        · simp only [Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
        · by_cases hx : x = .loc hl1 hl2
          · simp only [hx, ne_eq, not_true_eq_false, if_false] at h ⊢
            exact ih _ (hlt hp) hp _ rfl r s' h hr
          · simp only [hx, ne_eq, not_false_eq_true, if_true, Prod.mk.injEq] at h ⊢
            obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

end EvaluateAddClock

open EvaluateAddClock in
/-- HOL `evaluate_add_clock`: a run that does not time out runs identically with
`extra` more clock, finishing with `extra` more clock. The free HOL variable
`extra` is the outermost binder; the statement has no other premise. -/
theorem evaluateAddClock {width : Nat} [NeZero width] {C F : Type} (extra : Nat) :
    ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F)
      (r : Option (StackSemResult width)) (s' : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, s') ∧ r ≠ some .timeOut →
      evaluate (p, { s with clock := s.clock + extra }) =
        (r, { s' with clock := s'.clock + extra }) :=
  fun p s r s' h => addClock_measure extra _ p s rfl r s' h.1 h.2

end Flapjack.Compiler.Backend.StackProps
