import Flapjack.Compiler.Backend.Semantics.StackSem.Clock
import Flapjack.Compiler.Backend.Semantics.StackSem.ClockControl
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
namespace Flapjack.StackSemEvaluateClock
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm
open StackSemEvaluate StackSemControl StackSemStateOps StackSemMeasure
/-- Canonical imported state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

local macro "leaf_clock" h:ident : tactic =>
  `(tactic| (
    repeat' (first | (simp only [Prod.mk.injEq] at $h:ident; obtain ⟨-, h2⟩ := $h; subst h2) | split at $h:ident | dsimp only at $h:ident)
    all_goals try simp [emptyEnv, decClock, setVar, setStore]
    all_goals omega))
/-- Flapjack clock-first well-founded induction infrastructure for the full
original evaluator clock law; no independent HOL declaration. -/
private theorem clockMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure → ∀ (result : Option (StackSemResult width))
        (post : StackSemStateFiniteExact width C F),
      evaluate (program,source) = (result,post) → post.clock ≤ source.clock := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm r s' h
  subst hm
  cases p
  case skip => rw [evaluate_skip] at h; leaf_clock h
  case halt v => rw [evaluate_halt] at h; leaf_clock h
  case ret v => rw [evaluate_ret] at h; leaf_clock h
  case raise v => rw [evaluate_raise] at h; leaf_clock h
  case «break» v => rw [evaluate_break] at h; leaf_clock h
  case «continue» v => rw [evaluate_continue] at h; leaf_clock h
  case get v n => rw [evaluate_get] at h; leaf_clock h
  case set n v => rw [evaluate_set] at h; leaf_clock h
  case opCurrHeap b d src => rw [evaluate_opCurrHeap] at h; leaf_clock h
  case tick => rw [evaluate_tick] at h; leaf_clock h
  case install a b c d e => rw [evaluate_install] at h; leaf_clock h
  case codeBufferWrite a b => rw [evaluate_codeBufferWrite] at h; leaf_clock h
  case dataBufferWrite a b => rw [evaluate_dataBufferWrite] at h; leaf_clock h
  case ffi n a b c d e => rw [evaluate_ffi] at h; leaf_clock h
  case locValue a b c => rw [evaluate_locValue] at h; leaf_clock h
  case stackAlloc n => rw [evaluate_stackAlloc] at h; leaf_clock h
  case stackFree n => rw [evaluate_stackFree] at h; leaf_clock h
  case stackLoad a b => rw [evaluate_stackLoad] at h; leaf_clock h
  case stackLoadAny a b => rw [evaluate_stackLoadAny] at h; leaf_clock h
  case stackStore a b => rw [evaluate_stackStore] at h; leaf_clock h
  case stackStoreAny a b => rw [evaluate_stackStoreAny] at h; leaf_clock h
  case stackGetSize a => rw [evaluate_stackGetSize] at h; leaf_clock h
  case stackSetSize a => rw [evaluate_stackSetSize] at h; leaf_clock h
  case bitmapLoad a b => rw [evaluate_bitmapLoad] at h; leaf_clock h
  case inst instruction =>
    rw [evaluate_inst] at h
    split at h
    · rename_i post execution
      have same := (Prod.mk.inj h).2
      subst s'
      exact StackSemClock.instClock instruction s post execution
    · leaf_clock h
  case alloc register =>
    rw [evaluate_alloc] at h
    split at h
    · leaf_clock h
    · split at h
      · rename_i word _
        exact StackSemClock.allocClock word () s s' r h
      · leaf_clock h
  case storeConsts first second stub =>
    rw [evaluate_storeConsts] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2))
    all_goals first
      | exact Nat.le_refl _
      | exact StackSemClock.storeConstSemClock first second s s' r h
  case shMemOp operation register address =>
    cases address with
    | addr registerAddress offset =>
    rw [evaluate_shMemOp] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2))
    all_goals first
      | exact Nat.le_refl _
      | exact StackSemClock.shMemOpClock operation register _ s s' r h
      | exact Nat.le_trans (StackSemClock.shMemOpClock operation register _ (decClock s) s' r h) (by simp [decClock])
  case seq first second =>
    apply StackSemClockControl.evaluateClockSeq first second s _ _ r s' h
    · intro result post execution
      exact ih _ (seq_first_measure_lt first second s) first s rfl result post execution
    · intro firstResult middle firstRun isNone result post execution
      have lower := seq_second_measure_lt first second s (evaluate (first,s))
      rw [firstRun] at lower
      exact ih _ lower second middle rfl result post execution
  case ite comparison register operand first second =>
    apply StackSemClockControl.evaluateClockIf comparison register operand first second s _ _ r s' h
    · intro left right leftLookup rightLookup compared result post execution
      exact ih _ (if_first_measure_lt comparison register operand first second s) first s rfl result post execution
    · intro left right leftLookup rightLookup compared result post execution
      exact ih _ (if_second_measure_lt comparison register operand first second s) second s rfl result post execution
  case loop body =>
    apply StackSemClockControl.evaluateClockLoop body s _ _ r s' h
    · intro result post execution
      exact ih _ (loop_body_measure_lt body s) body s rfl result post execution
    · intro firstResult middle bodyRun continues nonzero result post execution
      have lower := loop_reentry_measure_lt body s (evaluate (body,s)) (by rw [bodyRun]; exact nonzero)
      rw [bodyRun] at lower
      exact ih _ lower (.loop body) (decClock middle) rfl result post execution
  case jumpLower r1 r2 dest =>
    rw [evaluate_jumpLower] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → t.clock ≤ s.clock → s'.clock ≤ s.clock := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    split at h
    · split at h
      · split at h
        · exact leaf _ _ h (by simp)
        · rename_i prog _
          split at h
          · exact leaf _ _ h (by simp [emptyEnv])
          · rename_i h0
            rcases h1 : evaluate (prog, decClock s) with ⟨res1, t1⟩
            rw [h1] at h
            have hc : t1.clock ≤ s.clock :=
              Nat.le_trans (ih _ (callee_measure_lt prog _ s h0) prog _ rfl res1 t1 h1) (by simp [decClock])
            dsimp only at h
            split at h
            · exact leaf _ _ h hc
            · exact leaf _ _ h hc
      · exact leaf _ _ h (by simp)
    · exact leaf _ _ h (by simp)
  case rawCall dest =>
    rw [evaluate_rawCall] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → t.clock ≤ s.clock → s'.clock ≤ s.clock := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    split at h
    · exact leaf _ _ h (by simp)
    · split at h
      · rename_i body _
        split at h
        · exact leaf _ _ h (by simp [emptyEnv])
        · rename_i h0
          rcases h1 : evaluate (body, decClock s) with ⟨r1, t1⟩
          rw [h1] at h
          have hc : t1.clock ≤ s.clock :=
            Nat.le_trans (ih _ (callee_measure_lt body _ s h0) body _ rfl r1 t1 h1) (by simp [decClock])
          dsimp only at h
          split at h
          · exact leaf _ _ h hc
          · exact leaf _ _ h hc
      · exact leaf _ _ h (by simp)
  case call ret dest handler =>
    rw [evaluate_call] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → t.clock ≤ s.clock → s'.clock ≤ s.clock := by
      intro x t he ht; simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he; exact ht
    cases ret with
    | none =>
      dsimp only at h
      split at h
      · exact leaf _ _ h (by simp)
      · rename_i prog _
        split at h
        · exact leaf _ _ h (by simp)
        · split at h
          · exact leaf _ _ h (by simp [emptyEnv])
          · rcases h1 : evaluate (prog, decClock s) with ⟨r1, t1⟩
            rw [h1] at h
            simp only [fixClock] at h
            have hc : min (decClock s).clock t1.clock ≤ s.clock := by
              simp only [decClock]
              omega
            by_cases hb : StackSemControl.badFunReturn r1 = true
            · simp only [hb, if_true] at h; exact leaf _ _ h hc
            · simp only [hb, Bool.false_eq_true, if_false] at h; exact leaf _ _ h hc
    | some rr =>
      obtain ⟨retH, link, l1, l2⟩ := rr
      dsimp only at h
      split at h
      · exact leaf _ _ h (by simp)
      · rename_i prog _
        split at h
        · exact leaf _ _ h (by simp [emptyEnv])
        · rename_i h0
          rcases h1 : evaluate (prog, decClock (setVar link (.loc l1 l2) s)) with ⟨r1, t1⟩
          rw [h1] at h
          have hfx : fixClock (decClock (setVar link (.loc l1 l2) s)) (r1, t1) =
              (r1, { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock }) := rfl
          have hlt := fun cont => call_continuation_measure_lt cont
            (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2 (r1, t1) h0
          have hc : min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock ≤ s.clock := by
            simp only [decClock, setVar]
            omega
          rw [hfx] at h hlt
          try dsimp only at h
          rcases r1 with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
          all_goals try (exact leaf _ _ h hc)
          · by_cases hx : x = .loc l1 l2
            · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
              exact Nat.le_trans (ih _ (hlt retH) retH _ rfl r s' h) hc
            · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
              exact leaf _ _ h hc
          · rcases handler with _ | ⟨hp, hl1, hl2⟩
            · exact leaf _ _ h hc
            · by_cases hx : x = .loc hl1 hl2
              · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
                exact Nat.le_trans (ih _ (hlt hp) hp _ rfl r s' h) hc
              · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
                exact leaf _ _ h hc
/-- Full original arbitrary-program clock inequality for the faithful native total evaluator.
No clock-law, callback, restricted-program or target-evaluation premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateClock {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : evaluate (program, source) = (result, post)) : post.clock ≤ source.clock :=
  clockMeasure _ program source rfl result post execution

/-- Full original unconditional identity: clamping an evaluation to its own input clock
leaves the actual evaluation unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fixClockEvaluate {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F) :
    fixClock source (evaluate (program, source)) = evaluate (program, source) := by
  rcases execution : evaluate (program, source) with ⟨result, post⟩
  simp only [fixClock]
  rw [Nat.min_eq_right (evaluateClock program source result post execution)]
end Flapjack.StackSemEvaluateClock
