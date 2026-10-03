import Flapjack.Compiler.Backend.LabFilter.Proofs.InstallCases
import Flapjack.Compiler.Backend.LabFilter.Proofs.PlainAsmErrorCases

namespace Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Full original native evaluator simulation. All case induction hypotheses are
proved internally by the decreasing source clock, including every Error and
TimeOut outcome. The result preserves the original whole execution and FFI
conclusion; no pass-success or target-execution premise is added. -/
@[hol "cakeml/compiler/backend/proofs/lab_filterProofScript.sml" "filter_correct"
  (words_as_type_indexed_bitvec)]
theorem filterCorrect {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F) :
    evaluate s1 = (res, s2) ∧ stateRel s1 t1 ∧ t1.failed = false →
    ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi := by
  suffices main : ∀ clock (s1 t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
      (res : MachineResult) (s2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      s1.clock = clock → evaluate s1 = (res, s2) → stateRel s1 t1 → t1.failed = false →
      ∃ extra t2, evaluate {t1 with clock := s1.clock + extra} = (res, t2) ∧ s2.ffi = t2.ffi by
    rintro ⟨heval, hrel, hfailed⟩
    exact main s1.clock s1 t1 res s2 rfl heval hrel hfailed
  intro clock
  induction clock using Nat.strong_induction_on with
  | h clock ih =>
    intro s1 t1 res s2 hclock heval hrel hfailed
    have recur : ∀ (next : Flapjack.Compiler.Backend.LabSem.State width C F),
        next.clock < s1.clock →
        ∀ (target : Flapjack.Compiler.Backend.LabSem.State width C F)
          (result : MachineResult) (final : Flapjack.Compiler.Backend.LabSem.State width C F),
        evaluate next = (result, final) → stateRel next target → target.failed = false →
        ∃ extra t2, evaluate {target with clock := next.clock + extra} = (result, t2) ∧ final.ffi = t2.ffi := by
      intro next hlt target result final he hr hf
      exact ih next.clock (by omega) next target result final rfl he hr hf
    by_cases hc : s1.clock = 0
    · exact filterCorrectClockZero s1 t1 res s2 heval hrel hfailed hc
    cases hf : asmFetch s1 with
    | none => exact filterCorrectAbsentFetch s1 t1 res s2 heval hrel hfailed hf
    | some line =>
      cases line with
      | label sid lid len => exact filterCorrectLabel s1 t1 res s2 sid lid len heval hrel hfailed hf
      | asm instruction bytes len =>
        cases instruction with
        | asmi instruction =>
          cases instruction with
          | inst instruction =>
            apply filterCorrectInstruction s1 t1 res s2 instruction bytes len heval hrel hfailed hf
            intro _ target result final _
            exact recur _ (by simp only [incPc, decClock, (asmInstConsts instruction s1).2.2.1]; omega) target result final
          | jump offset => exact filterCorrectPlainJump s1 t1 res s2 offset bytes len heval hrel hfailed hf
          | jumpCmp cmp register operand offset =>
            exact filterCorrectPlainJumpCmp s1 t1 res s2 cmp register operand offset bytes len heval hrel hfailed hf
          | call offset => exact filterCorrectPlainCall s1 t1 res s2 offset bytes len heval hrel hfailed hf
          | loc register offset => exact filterCorrectPlainLoc s1 t1 res s2 register offset bytes len heval hrel hfailed hf
          | jumpReg register =>
            cases hr : s1.regs register with
            | word value => exact filterCorrectJumpRegWord s1 t1 res s2 register value bytes len heval hrel hfailed hf hr
            | loc sid lid =>
              apply filterCorrectJumpRegLoc s1 t1 res s2 register sid lid bytes len heval hrel hfailed hf hr
              intro _ pc _
              exact recur _ (by simp only [updPc, decClock]; omega)
        | cbw r1 r2 =>
          apply filterCorrectBufferWrite s1 t1 res s2 r1 r2 bytes len heval hrel hfailed hf
          intro _ address value buffer _ _ _
          exact recur _ (by simp only [incPc, decClock]; omega)
        | shareMem operator register address =>
          apply filterCorrectSharedMemory s1 t1 res s2 operator register address bytes len heval hrel hfailed hf
          intro _ ffi returned next hshare
          have hn := shareMemOp_ret_clock operator register address s1 next ffi returned hshare
          exact recur _ (by change next.clock < s1.clock; omega)
      | labAsm instruction position bytes len =>
        cases instruction with
        | jump label =>
          apply filterCorrectJump s1 t1 res s2 label position bytes len heval hrel hfailed hf
          intro _ pc _
          exact recur _ (by simp only [updPc, decClock]; omega)
        | jumpCmp cmp register operand label =>
          cases hcmp : wordSemWordCmp cmp (s1.regs register) (regImm operand s1) with
          | none => exact filterCorrectJumpCmpNone s1 t1 res s2 cmp register operand label position bytes len heval hrel hfailed hf hcmp
          | some value =>
            cases value with
            | false =>
              apply filterCorrectJumpCmpFalse s1 t1 res s2 cmp register operand label position bytes len heval hrel hfailed hf hcmp
              intro _
              exact recur _ (by simp only [incPc, decClock]; omega)
            | true =>
              apply filterCorrectJumpCmpTrue s1 t1 res s2 cmp register operand label position bytes len heval hrel hfailed hf hcmp
              intro _ pc _
              exact recur _ (by simp only [updPc, decClock]; omega)
        | call label =>
          apply filterCorrectCall s1 t1 res s2 label position bytes len heval hrel hfailed hf
          intro _ pc location _ _
          exact recur _ (by simp only [updPc, decClock, updReg]; omega)
        | locValue register label =>
          apply filterCorrectLocValue s1 t1 res s2 register label position bytes len heval hrel hfailed hf
          intro _ _
          exact recur _ (by simp only [incPc, decClock, updReg]; omega)
        | halt => exact filterCorrectHalt s1 t1 res s2 position bytes len heval hrel hfailed hf
        | install =>
          apply filterCorrectInstall s1 t1 res s2 position bytes len heval hrel hfailed hf
          intro _ program installedSection pc buffer _
          exact recur _ (by change s1.clock - 1 < s1.clock; omega)
        | callFFI function =>
          apply filterCorrectCallFfi s1 t1 res s2 function position bytes len heval hrel hfailed hf
          intro _ start2 pc ffi returned _
          exact recur _ (by change s1.clock - 1 < s1.clock; omega)

end Flapjack.Compiler.Backend.LabFilter.Proofs
