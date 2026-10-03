import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.StackAccess

namespace Flapjack.Test.StackRawCallStackAccessParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.StackAccessCase

example {width : Nat} [NeZero width] {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.locValue register first second, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.locValue register first second)) info target post result ∧
    SimulationResult (comp info (.locValue register first second)) info target post result :=
  compCorrectLocValue register first second info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (execution : StackSemEvaluate.evaluate (.locValue register first second, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.locValue register first second)) info target post result ∧
    SimulationResult (comp info (.locValue register first second)) info target post result :=
  compCorrectLocValue register first second info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackAlloc n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackAlloc n)) info target post result ∧
    SimulationResult (comp info (.stackAlloc n)) info target post result :=
  compCorrectStackAlloc n info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (execution : StackSemEvaluate.evaluate (.stackAlloc n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackAlloc n)) info target post result ∧
    SimulationResult (comp info (.stackAlloc n)) info target post result :=
  compCorrectStackAlloc n info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackFree n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackFree n)) info target post result ∧
    SimulationResult (comp info (.stackFree n)) info target post result :=
  compCorrectStackFree n info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (execution : StackSemEvaluate.evaluate (.stackFree n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackFree n)) info target post result ∧
    SimulationResult (comp info (.stackFree n)) info target post result :=
  compCorrectStackFree n info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackLoad r n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackLoad r n)) info target post result ∧
    SimulationResult (comp info (.stackLoad r n)) info target post result :=
  compCorrectStackLoad r n info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (execution : StackSemEvaluate.evaluate (.stackLoad r n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackLoad r n)) info target post result ∧
    SimulationResult (comp info (.stackLoad r n)) info target post result :=
  compCorrectStackLoad r n info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackLoadAny r rn, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackLoadAny r rn)) info target post result ∧
    SimulationResult (comp info (.stackLoadAny r rn)) info target post result :=
  compCorrectStackLoadAny r rn info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (execution : StackSemEvaluate.evaluate (.stackLoadAny r rn, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackLoadAny r rn)) info target post result ∧
    SimulationResult (comp info (.stackLoadAny r rn)) info target post result :=
  compCorrectStackLoadAny r rn info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackStore r n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackStore r n)) info target post result ∧
    SimulationResult (comp info (.stackStore r n)) info target post result :=
  compCorrectStackStore r n info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (execution : StackSemEvaluate.evaluate (.stackStore r n, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackStore r n)) info target post result ∧
    SimulationResult (comp info (.stackStore r n)) info target post result :=
  compCorrectStackStore r n info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackStoreAny r rn, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackStoreAny r rn)) info target post result ∧
    SimulationResult (comp info (.stackStoreAny r rn)) info target post result :=
  compCorrectStackStoreAny r rn info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (execution : StackSemEvaluate.evaluate (.stackStoreAny r rn, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackStoreAny r rn)) info target post result ∧
    SimulationResult (comp info (.stackStoreAny r rn)) info target post result :=
  compCorrectStackStoreAny r rn info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackGetSize r, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackGetSize r)) info target post result ∧
    SimulationResult (comp info (.stackGetSize r)) info target post result :=
  compCorrectStackGetSize r info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (execution : StackSemEvaluate.evaluate (.stackGetSize r, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackGetSize r)) info target post result ∧
    SimulationResult (comp info (.stackGetSize r)) info target post result :=
  compCorrectStackGetSize r info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.stackSetSize r, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackSetSize r)) info target post result ∧
    SimulationResult (comp info (.stackSetSize r)) info target post result :=
  compCorrectStackSetSize r info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (execution : StackSemEvaluate.evaluate (.stackSetSize r, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.stackSetSize r)) info target post result ∧
    SimulationResult (comp info (.stackSetSize r)) info target post result :=
  compCorrectStackSetSize r info source target post result ⟨execution, nonerror, relation⟩

example {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.bitmapLoad r v, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.bitmapLoad r v)) info target post result ∧
    SimulationResult (comp info (.bitmapLoad r v)) info target post result :=
  compCorrectBitmapLoad r v info source target post result ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r v : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (execution : StackSemEvaluate.evaluate (.bitmapLoad r v, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.bitmapLoad r v)) info target post result ∧
    SimulationResult (comp info (.bitmapLoad r v)) info target post result :=
  compCorrectBitmapLoad r v info source target post result ⟨execution, nonerror, relation⟩

end Flapjack.Test.StackRawCallStackAccessParity
