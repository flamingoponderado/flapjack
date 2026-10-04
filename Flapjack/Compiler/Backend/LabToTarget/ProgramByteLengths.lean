import Flapjack.Compiler.Backend.LabToTarget.ByteLengths
import Flapjack.Compiler.Backend.LabToTarget.ValidityNop
import Flapjack.Compiler.Backend.LabToTarget.LengthCorrectness
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Complete original physical-byte sum law. The unused n has an independent
HOL type beta and remains an explicit generic binder without specialization. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_lengthProgToBytes {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) {β : Type u} (_n : β)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) :
    allEncOk c labs ffis pos code →
    (code.map (fun sec => (sec.lines.map lineLength).sum)).sum =
      (progToBytes code).length := by
  clear _n
  induction code generalizing pos with
  | nil => simp [progToBytes]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    intro h
    have hh := (allEncOk_cons c labs ffis lines pos sid rest).mp h
    have ht := ih _ hh.1
    rw [progToBytesMap]
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.length_append,List.length_flatten]
    rw [linesOk_mapLineByteLength lines c labs ffis pos hh.2.2]
    rw [progToBytesMap,List.length_flatten] at ht
    exact congrArg ((lines.map lineLength).sum + ·) ht

/-- Complete original section-fold law, retaining an arbitrary initial Nat
independently of the encoding-validity start position. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOk_foldSecLength {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (n : Nat)
    (c : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) :
    allEncOk c labs ffis pos code →
    code.foldl (fun start sec => secLength sec.lines start) n =
      (progToBytes code).length + n := by
  induction code generalizing n pos with
  | nil => simp [progToBytes]
  | cons sec rest ih =>
    rcases sec with ⟨sid,lines⟩
    intro h
    have hh := (allEncOk_cons c labs ffis lines pos sid rest).mp h
    have hlen := linesEncWithNop_lengthOk c.encode labs ffis pos lines
      (linesOk_linesEncWithNop c labs ffis pos lines hh.2.2)
    simp only [List.foldl_cons]
    rw [secLength_sumLineLength lines n hlen,ih _ _ hh.1]
    have hbytes : (progToBytes (⟨sid,lines⟩::rest)).length =
        (lines.map lineLength).sum + (progToBytes rest).length := by
      rw [progToBytesMap]
      simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_flatten]
      rw [linesOk_mapLineByteLength lines c labs ffis pos hh.2.2]
      rw [progToBytesMap]
      simp only [List.length_flatten]
    rw [hbytes]
    omega
end Flapjack.Compiler.Backend.LabToTarget
