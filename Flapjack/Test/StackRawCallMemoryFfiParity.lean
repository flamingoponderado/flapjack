import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.MemoryFfi
namespace Flapjack.Test.StackRawCallMemoryFfiParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.MemoryFfiCase

example {width : Nat} [NeZero width] {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectShMemOp op r a w
    info source target resultState result hypothesis

example {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec 1) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectShMemOp op r a w
    info source target resultState result hypothesis

example {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec 8) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectShMemOp op r a w
    info source target resultState result hypothesis

example {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec 64) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectShMemOp op r a w
    info source target resultState result hypothesis

example {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec 80) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResult (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectShMemOp op r a w
    info source target resultState result hypothesis

example {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectCodeBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectCodeBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectCodeBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectCodeBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectCodeBufferWrite r1 r2
    info source target resultState result hypothesis

example {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectDataBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectDataBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectDataBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectDataBufferWrite r1 r2
    info source target resultState result hypothesis

example {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResult (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectDataBufferWrite r1 r2
    info source target resultState result hypothesis

example {width : Nat} [NeZero width] {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectFfi function ptr len ptr2 len2 ret
    info source target resultState result hypothesis

example {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectFfi function ptr len ptr2 len2 ret
    info source target resultState result hypothesis

example {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectFfi function ptr len ptr2 len2 ret
    info source target resultState result hypothesis

example {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectFfi function ptr len ptr2 len2 ret
    info source target resultState result hypothesis

example {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResult (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectFfi function ptr len ptr2 len2 ret
    info source target resultState result hypothesis
end Flapjack.Test.StackRawCallMemoryFfiParity
