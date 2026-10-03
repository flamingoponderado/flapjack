import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall

namespace Flapjack.Test.StackRawCallCaseParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase

example {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (ih : CalleeIH C F dest source)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target post result ∧
    SimulationResult (comp info (.rawCall dest)) info target post result :=
  compCorrectRawCall dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (ih : CalleeIH C F dest source)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target post result ∧
    SimulationResult (comp info (.rawCall dest)) info target post result :=
  compCorrectRawCall dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (ih : CalleeIH C F dest source)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target post result ∧
    SimulationResult (comp info (.rawCall dest)) info target post result :=
  compCorrectRawCall dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (ih : CalleeIH C F dest source)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target post result ∧
    SimulationResult (comp info (.rawCall dest)) info target post result :=
  compCorrectRawCall dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (ih : CalleeIH C F dest source)
    (execution : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.rawCall dest)) info target post result ∧
    SimulationResult (comp info (.rawCall dest)) info target post result :=
  compCorrectRawCall dest info source target post result ih ⟨execution, nonerror, relation⟩

end Flapjack.Test.StackRawCallCaseParity
