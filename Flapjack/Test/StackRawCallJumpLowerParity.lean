import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.JumpLower

namespace Flapjack.Test.StackRawCallJumpLowerParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
open Flapjack.Compiler.Encoders.Asm

example {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (ih : JumpIH C F r1 r2 dest source)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result :=
  compCorrectJumpLower r1 r2 dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1)) (ih : JumpIH C F r1 r2 dest source)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result :=
  compCorrectJumpLower r1 r2 dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8)) (ih : JumpIH C F r1 r2 dest source)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result :=
  compCorrectJumpLower r1 r2 dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64)) (ih : JumpIH C F r1 r2 dest source)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result :=
  compCorrectJumpLower r1 r2 dest info source target post result ih ⟨execution, nonerror, relation⟩

example {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80)) (ih : JumpIH C F r1 r2 dest source)
    (execution : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    SimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result :=
  compCorrectJumpLower r1 r2 dest info source target post result ih ⟨execution, nonerror, relation⟩

example : wordCmpHOL .lower (BitVec.ofNat 1 0) (BitVec.ofNat 1 1) = true := by decide
example : wordCmpHOL .lower (BitVec.ofNat 1 1) (BitVec.ofNat 1 0) = false := by decide
example : wordCmpHOL .lower (BitVec.ofNat 8 255) (BitVec.ofNat 8 1) = false := by decide
example : wordCmpHOL .lower (BitVec.ofNat 64 0) (BitVec.ofNat 64 (2^63)) = true := by decide
example : wordCmpHOL .lower (BitVec.ofNat 64 (2^63)) (BitVec.ofNat 64 0) = false := by decide
example : wordCmpHOL .lower (BitVec.ofNat 80 0) (BitVec.ofNat 80 (2^79)) = true := by decide

def runChecks : IO Bool := do
  let ok := (wordCmpHOL .lower (BitVec.ofNat 1 0) (BitVec.ofNat 1 1) == true) &&
    (wordCmpHOL .lower (BitVec.ofNat 1 1) (BitVec.ofNat 1 0) == false) &&
    (wordCmpHOL .lower (BitVec.ofNat 8 255) (BitVec.ofNat 8 1) == false) &&
    (wordCmpHOL .lower (BitVec.ofNat 64 0) (BitVec.ofNat 64 (2^63)) == true) &&
    (wordCmpHOL .lower (BitVec.ofNat 64 (2^63)) (BitVec.ofNat 64 0) == false) &&
    (wordCmpHOL .lower (BitVec.ofNat 80 0) (BitVec.ofNat 80 (2^79)) == true)
  IO.println (if ok then "PASS original JumpLower unsigned comparisons (6) and full consumers (5)" else "FAIL JumpLower unsigned comparisons")
  pure ok

end Flapjack.Test.StackRawCallJumpLowerParity
