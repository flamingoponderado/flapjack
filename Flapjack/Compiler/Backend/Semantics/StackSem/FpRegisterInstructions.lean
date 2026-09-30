import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Misc.MachineIeee
import Flapjack.Misc.BinaryIeeeArith

/-! StackSem inst_def FP movement/sign and FP comparison/arithmetic case
fragment. Outer NONE means an unhandled constructor; inner NONE is HOL
instruction failure. This is untagged Flapjack assembly infrastructure, not a
port of the whole inst_def. The comparison cases follow HOL `inst_def`
(`cakeml/compiler/backend/semantics/stackSemScript.sml:519-542`); the
arithmetic cases follow `:563-587`, with the `FPFma` fused multiply-add
permutation of `fpSem$fpfma` (`cakeml/semantics/fpSemScript.sml:60-62`).
Real conversions (FPSqrt/FPToInt/FPFromInt) and whole evaluator routing remain
separate. -/
namespace Flapjack.StackSemFpRegisterInstructions
open StackSemStateOps Compiler.Encoders.Asm

/-- Exact-state case dispatch for FPLess/FPLessEqual/FPEqual, FPAdd/FPSub/
FPMul/FPDiv, FPFma, FPMov, FPAbs, FPNeg and the two FP/general register
transfers. Missing FP operands yield the inner HOL instruction failure. The
64-bit transfer path ignores the second register; other widths use low/high
extraction and high@@low concatenation, even at unusual widths. Nested setVar
order preserves HOL's behavior when destinations coincide. -/
noncomputable def instFpRegister {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemStateFiniteExact width C F)) :=
  match instruction with
  | .fp (.fpMov destination source) => some (
      match getFpVar source s with
      | some word => some (setFpVar destination word s)
      | none => none)
  | .fp (.fpAbs destination source) => some (
      match getFpVar source s with
      | some word => some (setFpVar destination (holFp64Abs word) s)
      | none => none)
  | .fp (.fpNeg destination source) => some (
      match getFpVar source s with
      | some word => some (setFpVar destination (holFp64Negate word) s)
      | none => none)
  | .fp (.fpLess r d1 d2) => some (
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 =>
          some (setVar r (.word (if holFp64LessThan f1 f2
            then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)
      | _, _ => none)
  | .fp (.fpLessEqual r d1 d2) => some (
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 =>
          some (setVar r (.word (if holFp64LessEqual f1 f2
            then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)
      | _, _ => none)
  | .fp (.fpEqual r d1 d2) => some (
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 =>
          some (setVar r (.word (if holFp64Equal f1 f2
            then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)
      | _, _ => none)
  | .fp (.fpAdd d1 d2 d3) => some (
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Add .roundTiesToEven f1 f2) s)
      | _, _ => none)
  | .fp (.fpSub d1 d2 d3) => some (
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Sub .roundTiesToEven f1 f2) s)
      | _, _ => none)
  | .fp (.fpMul d1 d2 d3) => some (
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Mul .roundTiesToEven f1 f2) s)
      | _, _ => none)
  | .fp (.fpDiv d1 d2 d3) => some (
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Div .roundTiesToEven f1 f2) s)
      | _, _ => none)
  | .fp (.fpFma d1 d2 d3) => some (
      match getFpVar d1 s, getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2, some f3 =>
          some (setFpVar d1 (holFp64MulAdd .roundTiesToEven f2 f3 f1) s)
      | _, _, _ => none)
  | .fp (.fpMovToReg r1 r2 source) => some (
      match getFpVar source s with
      | none => none
      | some word =>
          if width = 64 then some (setVar r1 (.word (word.setWidth width)) s)
          else some (setVar r2 (.word ((word.extractLsb' 32 32).setWidth width))
            (setVar r1 (.word ((word.extractLsb' 0 32).setWidth width)) s)))
  | .fp (.fpMovFromReg destination r1 r2) => some (
      if width = 64 then
        match getVar r1 s with
        | some (.word word) => some (setFpVar destination (word.setWidth 64) s)
        | _ => none
      else
        match getVar r1 s, getVar r2 s with
        | some (.word low), some (.word high) =>
            some (setFpVar destination ((high ++ low).setWidth 64) s)
        | _, _ => none)
  | _ => none

/-- Flapjack assembly certificate: every successful register/sign case
preserves clock, stack and memory. No success-state relation is assumed. -/
theorem instFpRegister_frame {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instFpRegister instruction s = some (some t)) :
    t.clock = s.clock ∧ t.stack = s.stack ∧ t.memory = s.memory := by
  cases instruction <;> simp [instFpRegister] at h
  case fp instruction =>
    cases instruction <;> simp at h
    all_goals repeat' split at h
    all_goals simp_all [getFpVar, getVar, setFpVar, setVar]
    all_goals rw [← h]
    all_goals exact ⟨rfl, rfl, rfl⟩

/-- Flapjack assembly certificate: below/above the 64-bit special case,
aliased destinations retain the high slice, because HOL writes it last. -/
theorem instFpRegister_toReg_alias {width : Nat} [NeZero width] {C F : Type}
    (register source : Nat) (word : BitVec 64)
    (s t : StackSemStateFiniteExact width C F)
    (hWidth : width ≠ 64) (hSource : getFpVar source s = some word)
    (h : instFpRegister (.fp (.fpMovToReg register register source)) s = some (some t)) :
    t.regs.lookup register = some (.word ((word.extractLsb' 32 32).setWidth width)) := by
  simp [instFpRegister, hWidth, hSource] at h
  cases h
  simp [setVar, FUPDATE_HOL]

/-- Flapjack assembly certificate: the 64-bit FromReg path needs only r1,
even when r2 is missing or location-valued. -/
theorem instFpRegister_fromReg64 {C F : Type} (destination r1 r2 : Nat)
    (word : BitVec 64) (s : StackSemStateFiniteExact 64 C F)
    (hSource : getVar r1 s = some (.word word)) :
    instFpRegister (.fp (.fpMovFromReg destination r1 r2)) s =
      some (some (setFpVar destination word s)) := by
  simp [instFpRegister, hSource]

end Flapjack.StackSemFpRegisterInstructions
