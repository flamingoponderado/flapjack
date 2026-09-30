import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Misc.MachineIeee

/-! StackSem inst_def FP movement/sign case fragment. Outer NONE means an
unhandled constructor; inner NONE is HOL instruction failure. This is untagged
Flapjack assembly infrastructure, not a port of the whole inst_def. Floating
arithmetic, real conversions, and whole evaluator routing remain separate. -/
namespace Flapjack.StackSemFpRegisterInstructions
open StackSemStateOps Compiler.Encoders.Asm

/-- Exact-state case dispatch for FPMov, FPAbs, FPNeg and the two FP/general
register transfers. The 64-bit path ignores the second register; other widths
use low/high extraction and high@@low concatenation, even at unusual widths.
Nested setVar order preserves HOL's behavior when destinations coincide. -/
def instFpRegister {width : Nat} [NeZero width] {C F : Type}
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
