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

end Flapjack.Test.LabToTargetInitializationContractsParity
