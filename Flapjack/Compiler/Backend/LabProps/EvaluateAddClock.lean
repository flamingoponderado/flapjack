import Flapjack.Compiler.Backend.LabProps.EvaluateAddClockIoEventsMono

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem

/-- Flapjack arithmetic infrastructure; no separate HOL original. -/
private theorem clockAddSub {clock extra : Nat} (hne : clock ≠ 0) :
    clock + extra - 1 = clock - 1 + extra := by omega

/-- Projection of asm_inst_consts; no separate HOL original. -/
private theorem asmInst_clock {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (asmInst i s).clock = s.clock := (asmInstConsts i s).2.2.1

/-- Flapjack result-accessor form used to prove the complete source statement. -/
private theorem evaluateClockShift {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (extra : Nat) :
    (evaluate s).1 ≠ .timeOut →
    evaluate { s with clock := s.clock + extra } =
      ((evaluate s).1, { (evaluate s).2 with clock := (evaluate s).2.clock + extra }) := by
  fun_induction evaluate s
  all_goals intro hresult
  all_goals try contradiction
  all_goals conv => lhs; rw [evaluate]
  case case12 s h op reg addr _ _ hf ffi bytes next hs hnextClock ih =>
    have hc := (shareMemOpAddClockSame s op reg addr extra ffi bytes next
      { name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed } s).2.1 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    simp only [asmFetch] at hf
    simp only [Nat.add_eq_zero_iff, h, false_and, ↓reduceIte, asmFetch, hf]
    rw [hc]
    simpa only [Nat.add_comm] using ih hresult
  all_goals simp_all +zetaDelta [clockAddSub, asmInst_clock, Nat.add_eq_zero_iff, asmFetch,
    asmInstWithClock, getPcValue, getRetLoc, regImm, incPc, decClock, updPc, updReg]

  case case10 s h op reg addr _ _ _ hs =>
    have hc := (shareMemOpAddClockSame s op reg addr extra s.ffi [] s
      { name := .sharedMem .mappedRead, configuration := [], bytes := [], outcome := .failed } s).1 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    rw [hc]
  case case11 s h op reg addr _ _ outcome next _ hs =>
    have hc := (shareMemOpAddClockSame s op reg addr extra s.ffi [] s outcome next).2.2 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    rw [hc]
    simp only [Nat.add_comm]
  case case28 => split <;> simp_all +zetaDelta

/-- Full original result and whole post-state clock extension, including Error.
Only TimeOut is excluded, as in HOL. Arbitrary compiler configuration and FFI
carriers remain independent. Evaluation inherits the real rendering assumption
of SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_ADD_clock"
  (words_as_type_indexed_bitvec)]
theorem evaluateAddClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (res : MachineResult)
    (r : Flapjack.Compiler.Backend.LabSem.State width C F) (extra : Nat) :
    evaluate s = (res, r) ∧ res ≠ .timeOut →
    evaluate { s with clock := s.clock + extra } =
      (res, { r with clock := r.clock + extra }) := by
  intro h
  have hn : (evaluate s).1 ≠ .timeOut := by simpa only [h.1] using h.2
  simpa only [h.1] using evaluateClockShift s extra hn

end Flapjack.Compiler.Backend.LabProps
