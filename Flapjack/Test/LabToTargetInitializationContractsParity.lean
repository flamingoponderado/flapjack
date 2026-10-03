import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts

namespace Flapjack.Test.LabToTargetInitializationContractsParity
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm

-- Arbitrary-width, arbitrary-oracle consumers retain every source clause.
example {width : Nat} [NeZero width]
    (oracle : Nat → Config × LabProgHOL width) (labs : Spt (Spt Nat))
    (pos : Nat) (c : AsmConfigExact width) (ffis : List HolFfiName) :
    compilerOracleOk oracle labs pos c ffis ↔
      (∀ k, goodCode c (oracle k).1.labels (oracle k).2 ∧
        Flapjack.Compiler.Backend.LabProps.noShareMemInst (oracle k).2) ∧
      ((oracle 0).1.labels = labs ∧ (oracle 0).1.pos = pos ∧
        (oracle 0).1.ffiNames = some ffis) := Iff.rfl

example {width : Nat} [NeZero width]
    (oracle : Nat → Config × LabProgHOL width) (labs : Spt (Spt Nat))
    (pos : Nat) (c : AsmConfigExact width) (ffis : List HolFfiName)
    (h : compilerOracleOk oracle labs pos c ffis) (k : Nat) :
    goodCode c (oracle k).1.labels (oracle k).2 := (h.1 k).1

example {width : Nat} [NeZero width]
    (oracle : Nat → Config × LabProgHOL width) (labs : Spt (Spt Nat))
    (pos : Nat) (c : AsmConfigExact width) (ffis : List HolFfiName)
    (h : compilerOracleOk oracle labs pos c ffis) (k : Nat) :
    Flapjack.Compiler.Backend.LabProps.noShareMemInst (oracle k).2 := (h.1 k).2

example {width : Nat} [NeZero width]
    (oracle : Nat → Config × LabProgHOL width) (labs : Spt (Spt Nat))
    (pos : Nat) (c : AsmConfigExact width) (ffis : List HolFfiName)
    (h : compilerOracleOk oracle labs pos c ffis) :
    (oracle 0).1.labels = labs ∧ (oracle 0).1.pos = pos ∧
      (oracle 0).1.ffiNames = some ffis := h.2

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) :
    mcConfOk mc ↔
      goodDimindex width ∧
      Flapjack.Compiler.Encoders.AsmProps.encoderCorrect mc.target ∧
      asmRegOkExact mc.ptrReg mc.target.config = true ∧
      asmRegOkExact mc.lenReg mc.target.config = true ∧
      asmRegOkExact mc.ptr2Reg mc.target.config = true ∧
      asmRegOkExact mc.len2Reg mc.target.config = true ∧
      asmRegOkExact (mc.target.config.linkReg.getD 0) mc.target.config = true ∧
      encOk mc.target.config := by
  unfold mcConfOk
  cases mc.target.config.linkReg <;> rfl

-- Intrinsic positive dimensions alone must not discharge the source guard.
example {S Q : Type} (mc : MachineConfig 8 S Q) : ¬ mcConfOk mc := by
  intro h
  simpa [goodDimindex] using h.1

example {S Q : Type} (mc : MachineConfig 128 S Q) : ¬ mcConfOk mc := by
  intro h
  simpa [goodDimindex] using h.1

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (h : mcConfOk mc) :
    targetOk mc.target :=
  Flapjack.Compiler.Encoders.AsmProps.encoderCorrect_targetOk h.2.1

end Flapjack.Test.LabToTargetInitializationContractsParity
