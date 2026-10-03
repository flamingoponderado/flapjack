import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.AllocationStore
namespace Flapjack.Test.StackRawCallAllocationStoreParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase

example {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result :=
  compCorrectAlloc register info source target post result hypothesis

example {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result :=
  compCorrectAlloc register info source target post result hypothesis

example {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result :=
  compCorrectAlloc register info source target post result hypothesis

example {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result :=
  compCorrectAlloc register info source target post result hypothesis

example {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.alloc register)) info target post result ∧
    SimulationResult (comp info (.alloc register)) info target post result :=
  compCorrectAlloc register info source target post result hypothesis

example {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result :=
  compCorrectStoreConsts first second stub info source target post result hypothesis

example {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result :=
  compCorrectStoreConsts first second stub info source target post result hypothesis

example {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result :=
  compCorrectStoreConsts first second stub info source target post result hypothesis

example {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result :=
  compCorrectStoreConsts first second stub info source target post result hypothesis

example {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResult (comp info (.storeConsts first second stub)) info target post result :=
  compCorrectStoreConsts first second stub info source target post result hypothesis

example {width : Nat} [NeZero width] (info : Spt Nat) (first second : Nat) :
    compTop info (.seq (.storeConsts first second none) (.ret 0)) =
      (.seq (.storeConsts first second none) (.ret 0) : HolProg width) := rfl

end Flapjack.Test.StackRawCallAllocationStoreParity
