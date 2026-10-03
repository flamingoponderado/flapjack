import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.AllocationConstants
import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock

/-! Work toward the full original StackProps `evaluate_io_events_mono`
(stackPropsScript.sml:454–475), a genuine prerequisite of the extra-clock
prefix theorem and StackRemove `compile_semantics`. The full theorem must
retain arbitrary native programs/states/results and its sole source-run
premise. Local helpers here are Flapjack-only case factoring, with no
independent HOL declarations. -/
namespace Flapjack.Compiler.Backend.StackProps.EvaluateIoEventsMono
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure

/-- Local instruction case: original successful instruction FFI preservation
implies the event prefix without any condition on the FP result. -/
theorem instructionEventsPrefix {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (source post : StackSemStateFiniteExact width C F)
    (execution : StackSemInst.instHOL instruction source = some post) :
    source.ffi.ioEvents <+: post.ffi.ioEvents := by
  rw [(StackPropsInstructionConstants.instConst instruction source post execution).1]


/-- Local shared-memory case, including errors and terminal FFI. Only an
actual successful oracle return can change the event list. -/
theorem sharedMemoryEventsPrefix {width : Nat} [NeZero width] {C F : Type}
    (operation : WordMemOp) (register : Nat) (address : BitVec width)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemShMem.shMemOp operation register address source = (result, post)) :
    source.ffi.ioEvents <+: post.ffi.ioEvents := by
  cases operation <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
      StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
      StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32] at execution
  all_goals repeat' split at execution
  all_goals rcases Prod.mk.inj execution with ⟨-, rfl⟩
  all_goals first
    | exact List.prefix_refl _
    | exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)

/-- Local full external-FFI constructor case. Every word-read/byte-array
failure and terminal outcome retains the state; a return uses the exact
shared call_FFI append law. -/
theorem ffiEventsPrefix {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength returnAddress : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate
      (.ffi name configuration configurationLength array arrayLength returnAddress, source) =
        (result, post)) :
    source.ffi.ioEvents <+: post.ffi.ioEvents := by
  rw [StackSemEvaluate.evaluate_ffi] at execution
  repeat' split at execution
  all_goals rcases Prod.mk.inj execution with ⟨-, rfl⟩
  all_goals first
    | exact List.prefix_refl _
    | exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ (by assumption)


/-- Local structural case simplification; no independent HOL declaration. -/
local macro "leaf_events" h:ident : tactic =>
  `(tactic| (
    repeat' (first | (simp only [Prod.mk.injEq] at $h:ident; obtain ⟨-, h2⟩ := $h; subst h2) | split at $h:ident | dsimp only at $h:ident)
    all_goals simp [emptyEnv, decClock, setVar, setStore]))
/-- Local induction on the original evaluator measure; no independent HOL declaration. -/
private theorem eventsMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure → ∀ (result : Option (StackSemResult width))
        (post : StackSemStateFiniteExact width C F),
      evaluate (program,source) = (result,post) → source.ffi.ioEvents <+: post.ffi.ioEvents := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm r s' h
  subst hm
  cases p
  case skip => rw [evaluate_skip] at h; leaf_events h
  case halt v => rw [evaluate_halt] at h; leaf_events h
  case ret v => rw [evaluate_ret] at h; leaf_events h
  case raise v => rw [evaluate_raise] at h; leaf_events h
  case «break» v => rw [evaluate_break] at h; leaf_events h
  case «continue» v => rw [evaluate_continue] at h; leaf_events h
  case get v n => rw [evaluate_get] at h; leaf_events h
  case set n v => rw [evaluate_set] at h; leaf_events h
  case opCurrHeap b d src => rw [evaluate_opCurrHeap] at h; leaf_events h
  case tick => rw [evaluate_tick] at h; leaf_events h
  case install a b c d e => rw [evaluate_install] at h; leaf_events h
  case codeBufferWrite a b => rw [evaluate_codeBufferWrite] at h; leaf_events h
  case dataBufferWrite a b => rw [evaluate_dataBufferWrite] at h; leaf_events h
  case ffi n a b c d e => exact ffiEventsPrefix n a b c d e s s' r h
  case locValue a b c => rw [evaluate_locValue] at h; leaf_events h
  case stackAlloc n => rw [evaluate_stackAlloc] at h; leaf_events h
  case stackFree n => rw [evaluate_stackFree] at h; leaf_events h
  case stackLoad a b => rw [evaluate_stackLoad] at h; leaf_events h
  case stackLoadAny a b => rw [evaluate_stackLoadAny] at h; leaf_events h
  case stackStore a b => rw [evaluate_stackStore] at h; leaf_events h
  case stackStoreAny a b => rw [evaluate_stackStoreAny] at h; leaf_events h
  case stackGetSize a => rw [evaluate_stackGetSize] at h; leaf_events h
  case stackSetSize a => rw [evaluate_stackSetSize] at h; leaf_events h
  case bitmapLoad a b => rw [evaluate_bitmapLoad] at h; leaf_events h

  case inst instruction =>
    rw [evaluate_inst] at h
    split at h
    · rename_i post execution
      have same := (Prod.mk.inj h).2
      subst s'
      exact instructionEventsPrefix instruction s post execution
    · leaf_events h
  case alloc register =>
    rw [evaluate_alloc] at h
    split at h
    · leaf_events h
    · split at h
      · rename_i word _
        rw [(StackPropsAllocationConstants.allocConst word s s' r h).1]
      · leaf_events h
  case storeConsts first second stub =>
    rw [evaluate_storeConsts] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2))
    all_goals first
      | exact List.prefix_refl _
      | rw [(StackPropsAllocationConstants.storeConstSemConst first second s s' r h).1]
  case shMemOp operation register address =>
    cases address with
    | addr registerAddress offset =>
    rw [evaluate_shMemOp] at h
    repeat' (first | split at h | (simp only [Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2))
    all_goals first
      | exact List.prefix_refl _
      | exact sharedMemoryEventsPrefix operation register _ s s' r h
      | exact sharedMemoryEventsPrefix operation register _ (decClock s) s' r h
  case seq first second =>
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at h
    rcases firstRun : evaluate (first,s) with ⟨firstResult, middle⟩
    rw [firstRun] at h
    have eventsPrefix := ih _ (seq_first_measure_lt first second s) first s rfl firstResult middle firstRun
    cases firstResult with
    | none =>
      have smaller := seq_second_measure_lt first second s (evaluate (first,s))
      rw [StackSemEvaluateClock.fixClockEvaluate, firstRun] at smaller
      exact eventsPrefix.trans (ih _ smaller second middle rfl r s' h)
    | some value =>
      exact (Prod.mk.inj h).2 ▸ eventsPrefix
  case ite comparison register operand first second =>
    rw [evaluate_ite] at h
    repeat' split at h
    all_goals first
      | exact ih _ (if_first_measure_lt comparison register operand first second s) first s rfl r s' h
      | exact ih _ (if_second_measure_lt comparison register operand first second s) second s rfl r s' h
      | leaf_events h
  case loop body =>
    rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at h
    rcases bodyRun : evaluate (body,s) with ⟨bodyResult, middle⟩
    rw [bodyRun] at h
    dsimp only at h
    have eventsPrefix := ih _ (loop_body_measure_lt body s) body s rfl bodyResult middle bodyRun
    by_cases continues : contLoop bodyResult = true
    · rw [if_pos continues] at h
      by_cases zero : middle.clock = 0
      · rw [if_pos zero] at h
        exact (Prod.mk.inj h).2 ▸ eventsPrefix
      · rw [if_neg zero] at h
        have smaller := loop_reentry_measure_lt body s (evaluate (body,s))
          (by rw [StackSemEvaluateClock.fixClockEvaluate, bodyRun]; exact zero)
        rw [StackSemEvaluateClock.fixClockEvaluate, bodyRun] at smaller
        exact eventsPrefix.trans (ih _ smaller (.loop body) (decClock middle) rfl r s' h)
    · rw [if_neg continues] at h
      exact (Prod.mk.inj h).2 ▸ eventsPrefix
  case jumpLower r1 r2 dest =>
    rw [evaluate_jumpLower] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → s.ffi.ioEvents <+: t.ffi.ioEvents → s.ffi.ioEvents <+: s'.ffi.ioEvents := by
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
            have hc : s.ffi.ioEvents <+: t1.ffi.ioEvents :=
              ih _ (callee_measure_lt prog _ s h0) prog _ rfl res1 t1 h1
            dsimp only at h
            split at h
            · exact leaf _ _ h hc
            · exact leaf _ _ h hc
      · exact leaf _ _ h (by simp)
    · exact leaf _ _ h (by simp)
  case rawCall dest =>
    rw [evaluate_rawCall] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → s.ffi.ioEvents <+: t.ffi.ioEvents → s.ffi.ioEvents <+: s'.ffi.ioEvents := by
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
          have hc : s.ffi.ioEvents <+: t1.ffi.ioEvents :=
            ih _ (callee_measure_lt body _ s h0) body _ rfl r1 t1 h1
          dsimp only at h
          split at h
          · exact leaf _ _ h hc
          · exact leaf _ _ h hc
      · exact leaf _ _ h (by simp)
  case call ret dest handler =>
    rw [evaluate_call] at h
    have leaf : ∀ (x : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
        (x, t) = (r, s') → s.ffi.ioEvents <+: t.ffi.ioEvents → s.ffi.ioEvents <+: s'.ffi.ioEvents := by
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
            have hc : s.ffi.ioEvents <+: t1.ffi.ioEvents :=
              ih _ (callee_measure_lt prog _ s (by assumption)) prog _ rfl r1 t1 h1
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
          have hc : s.ffi.ioEvents <+: t1.ffi.ioEvents :=
            ih _ (callee_measure_lt prog _ (setVar link (.loc l1 l2) s) h0) prog _ rfl r1 t1 h1
          rw [hfx] at h hlt
          try dsimp only at h
          rcases r1 with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
          all_goals try (exact leaf _ _ h hc)
          · by_cases hx : x = .loc l1 l2
            · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
              exact hc.trans (ih _ (hlt retH) retH _ rfl r s' h)
            · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
              exact leaf _ _ h hc
          · rcases handler with _ | ⟨hp, hl1, hl2⟩
            · exact leaf _ _ h hc
            · by_cases hx : x = .loc hl1 hl2
              · simp only [hx, ne_eq, not_true_eq_false, if_false] at h
                exact hc.trans (ih _ (hlt hp) hp _ rfl r s' h)
              · simp only [hx, ne_eq, not_false_eq_true, if_true] at h
                exact leaf _ _ h hc

/-- Canonical codec for the actual imported native evaluator state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original `evaluate_io_events_mono` (454–475). Retains arbitrary
programs, source/result/poststate and its sole native evaluation premise.
The original clock-first measure derives every recursive premise; the
exact call_FFI law handles both external and shared-memory event changes.
The evaluator closure inherits the reviewed reals_as_rational_cuts carrier
(SOUNDNESS item 8); event preservation does not assert FP numerical parity. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateIoEventsMono {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    source.ffi.ioEvents <+: post.ffi.ioEvents :=
  eventsMeasure (StackSemMeasure.stackSemMeasure program source) program source rfl result post execution

end Flapjack.Compiler.Backend.StackProps.EvaluateIoEventsMono
