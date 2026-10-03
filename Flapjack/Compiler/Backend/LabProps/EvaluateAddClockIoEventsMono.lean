import Flapjack.Compiler.Backend.LabProps.EvaluateIoEventsMono
import Flapjack.Compiler.Backend.LabProps.ClockSupport

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem

/-- Flapjack arithmetic consequence for nonzero source clocks; no separate HOL original. -/
private theorem clockAddSub {clock extra : Nat} (hne : clock ≠ 0) :
    clock + extra - 1 = clock - 1 + extra := by omega

/-- Projection of the already ported asm_inst_consts conjunction; no new HOL declaration. -/
private theorem asmInst_clock {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (asmInst i s).clock = s.clock := (asmInstConsts i s).2.2.1

/-- Full original clock extension law; arbitrary native state and extra clock,
with no success, target execution or event-prefix assumption. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_add_clock_io_events_mono"
  (words_as_type_indexed_bitvec)]
theorem evaluateAddClockIoEventsMono {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (extra : Nat) :
    (evaluate s).2.ffi.ioEvents <+:
      (evaluate { s with clock := s.clock + extra }).2.ffi.ioEvents := by
  fun_induction evaluate s
  case case1 s _ =>
    exact evaluateIoEventsMono { s with clock := s.clock + extra }
      (evaluate { s with clock := s.clock + extra }).1
      (evaluate { s with clock := s.clock + extra }).2 rfl
  all_goals try exact List.prefix_refl _
  all_goals conv => rhs; rw [evaluate]
  all_goals simp_all +zetaDelta [clockAddSub, asmInst_clock, Nat.add_eq_zero_iff, asmFetch,
    asmInstWithClock, getPcValue, getRetLoc, regImm, incPc, decClock, updPc, updReg]
  all_goals try first | exact List.prefix_refl _ | assumption

  -- The final-event literals below instantiate only vacuous binders of other
  -- conjunction clauses; they are never evaluated and impose no FFI policy.
  case case10 s h op reg addr _ _ _ hs =>
    have hc := (shareMemOpAddClockSame s op reg addr extra s.ffi [] s
      { name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed } s).1 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    rw [hc]
    exact List.prefix_refl _
  case case11 s h op reg addr _ _ outcome next _ hs =>
    have hc := (shareMemOpAddClockSame s op reg addr extra s.ffi [] s outcome next).2.2 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    rw [hc]
    exact List.prefix_refl _
  case case12 s h op reg addr _ _ ffi bytes next _ hs hnextClock ih =>
    have hc := (shareMemOpAddClockSame s op reg addr extra ffi bytes next
      { name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed } s).2.1 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    rw [hc]
    simpa only [Nat.add_comm, hnextClock] using ih
  case case28 => split <;> simp_all +zetaDelta

/-- Flapjack consequence for constructing observational prefix chains: the
actual traces at any two source clocks are comparable. No separately named HOL
declaration owns this consequence; it asserts no target simulation. -/
theorem evaluatedClockTracesComparable {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (k1 k2 : Nat) :
    (evaluate { s with clock := k1 }).2.ffi.ioEvents <+:
        (evaluate { s with clock := k2 }).2.ffi.ioEvents ∨
      (evaluate { s with clock := k2 }).2.ffi.ioEvents <+:
        (evaluate { s with clock := k1 }).2.ffi.ioEvents := by
  rcases Nat.le_total k1 k2 with h | h
  · left
    have heq : k1 + (k2 - k1) = k2 := by omega
    simpa only [heq] using evaluateAddClockIoEventsMono { s with clock := k1 } (k2 - k1)
  · right
    have heq : k2 + (k1 - k2) = k1 := by omega
    simpa only [heq] using evaluateAddClockIoEventsMono { s with clock := k2 } (k1 - k2)

end Flapjack.Compiler.Backend.LabProps
