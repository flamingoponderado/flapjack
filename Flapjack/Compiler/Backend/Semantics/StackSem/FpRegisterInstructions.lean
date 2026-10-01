import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Misc.MachineIeee
import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.Misc.BinaryIeeeSqrt.RoundAgreement
import Flapjack.Misc.BinaryIeeeConvert
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

/-! StackSem inst_def FP movement/sign, FP comparison/arithmetic and FP real
conversion case fragment. Outer NONE means an unhandled constructor; inner NONE
is HOL instruction failure. This is untagged Flapjack assembly infrastructure,
not a port of the whole inst_def. The comparison cases follow HOL `inst_def`
(`cakeml/compiler/backend/semantics/stackSemScript.sml:519-542`); the
arithmetic cases follow `:563-587`, with the `FPFma` fused multiply-add
permutation of `fpSem$fpfma` (`cakeml/semantics/fpSemScript.sml:60-62`); the
conversions follow `FPSqrt` `:558-562`, `FPToInt` `:605-623` and `FPFromInt`
`:624-636`, with `FPSqrt` rendered through the faithful real-sqrt
`holFp64SqrtReal` (`Flapjack/Misc/BinaryIeeeSqrt/RoundAgreement.lean`, proven
equal to the rational-cut `holFp64Sqrt` by `holFp64Sqrt_tiesToEven_agreement`).
Whole evaluator routing remains separate. -/
namespace Flapjack.StackSemFpRegisterInstructions
open StackSemStateOps Compiler.Encoders.Asm

namespace FiniteSupport

/-- Same-module canonical finite-map roundtrip witness for the owning carrier
`StackSemStateFiniteExact`, forwarded from the accepted `StateOps` witness;
qualifier infrastructure only. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end FiniteSupport

/-- HOL `inst_def` FPSqrt constructor case
(`cakeml/compiler/backend/semantics/stackSemScript.sml:558-562`), split along
HOL's own case structure. Reads the source FP register and, when present,
writes the faithful real-sqrt rendering `holFp64SqrtReal` at round-ties-to-even
into the destination; a missing source yields the inner HOL instruction failure.
The stated result is exactly the clause's `Option state` value, with no extra
dispatcher `some`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" 409
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def instFpSqrt {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  match getFpVar d2 s with
  | some f => some (setFpVar d1 (holFp64SqrtReal .roundTiesToEven f) s)
  | none => none

/-- HOL `inst_def` FPToInt constructor case
(`cakeml/compiler/backend/semantics/stackSemScript.sml:605-623`), split along
HOL's own case structure. Reads the source FP register, converts with
`holFp64ToInt` at round-ties-to-even, re-encodes as a `word32` `i2w i`, and only
proceeds when `w2i w = i`. At 64 bits it widens `w2w`; otherwise it splices `w`
into the low/high half of register `d1 DIV 2` with `bit_field_insert`, selecting
the high half exactly when `ODD d1`. Missing operands and non-representable
integers yield the inner HOL instruction failure; the stated result is exactly
the clause's `Option state` value. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" 409
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
noncomputable def instFpToInt {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  match getFpVar d2 s with
  | none => none
  | some f =>
      match holFp64ToInt .roundTiesToEven f with
      | none => none
      | some i =>
          let w : BitVec 32 := BitVec.ofInt 32 i
          if w.toInt = i then
            (if width = 64 then some (setFpVar d1 (w.setWidth 64) s)
             else
              match getFpVar (d1 / 2) s with
              | none => none
              | some f =>
                  let (h, l) := if d1 % 2 = 1 then (63, 32) else (31, 0)
                  some (setFpVar (d1 / 2) (holBitFieldInsert h l w f) s))
          else none

/-- HOL `inst_def` FPFromInt constructor case
(`cakeml/compiler/backend/semantics/stackSemScript.sml:624-636`), split along
HOL's own case structure. At 64 bits it extracts the low 32 bits of the source
FP register; otherwise it reads the selected low/high half of register
`d2 DIV 2` (`ODD d2` selects the high half). The extracted word is converted
with `holIntToFp64` at round-ties-to-even and written to the destination. A
missing source yields the inner HOL instruction failure; the stated result is
exactly the clause's `Option state` value. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "inst_def" 409
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)
  (reals_as_rational_cuts)]
noncomputable def instFpFromInt {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemStateFiniteExact width C F) :=
  if width = 64 then
    match getFpVar d2 s with
    | some f =>
        let i := (holWordExtract 31 0 f 32).toInt
        some (setFpVar d1 (holIntToFp64 .roundTiesToEven i) s)
    | none => none
  else
    match getFpVar (d2 / 2) s with
    | some v =>
        let i := (if d2 % 2 = 1 then holWordExtract 63 32 v width
          else holWordExtract 31 0 v width).toInt
        some (setFpVar d1 (holIntToFp64 .roundTiesToEven i) s)
    | none => none

/-- Exact-state case dispatch for FPLess/FPLessEqual/FPEqual, FPAdd/FPSub/
FPMul/FPDiv, FPFma, FPMov, FPAbs, FPNeg, FPSqrt, FPToInt, FPFromInt and the two
FP/general register transfers. Missing FP operands yield the inner HOL
instruction failure. The 64-bit transfer path ignores the second register;
other widths use low/high extraction and high@@low concatenation, even at
unusual widths. FPToInt stores the `word32` directly at 64 bits and otherwise
splices it into the low/high half of register `d1 DIV 2` (`ODD d1` selects the
high half); FPFromInt reads the low 32 bits at 64 bits and otherwise reads the
selected half of register `d2 DIV 2`. Nested setVar order preserves HOL's
behavior when destinations coincide. -/
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
  | .fp (.fpSqrt d1 d2) => some (instFpSqrt d1 d2 s)
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
  | .fp (.fpToInt d1 d2) => some (instFpToInt d1 d2 s)
  | .fp (.fpFromInt d1 d2) => some (instFpFromInt d1 d2 s)
  | _ => none

/-- Flapjack assembly certificate: every successful register/sign case
preserves clock, stack and memory. No success-state relation is assumed. -/
theorem instFpRegister_frame {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instFpRegister instruction s = some (some t)) :
    t.clock = s.clock ∧ t.stack = s.stack ∧ t.memory = s.memory := by
  cases instruction <;> simp [instFpRegister, instFpSqrt, instFpToInt, instFpFromInt] at h
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
