import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Standard
namespace Flapjack.Test.StackRawCallSeqStandardParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.SeqCase

example {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result :=
  simulateStandardSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 1) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result :=
  simulateStandardSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 8) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result :=
  simulateStandardSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 64) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result :=
  simulateStandardSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 80) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (.seq (comp info first) (comp info second)) info target post result :=
  simulateStandardSeq first second info source target post result firstIH secondIH hypothesis

-- Original standard compiler observations, checked independently by kernel
-- reduction and executable guards. The full optimized case remains open.
example {width : Nat} [NeZero width] (info : Spt Nat) :
    compTop info (.seq .skip .skip : HolProg width) = .seq .skip .skip ∧
    comp info (.seq .skip .skip : HolProg width) = .seq .skip .skip := by
  simp [compTop, comp, compSeq, destCase]
#guard match comp (.ln : Spt Nat) (.seq .skip .skip : HolProg 64) with
  | .seq .skip .skip => true
  | _ => false
#guard match comp (.ln : Spt Nat) (.seq .skip .skip : HolProg 80) with
  | .seq .skip .skip => true
  | _ => false
end Flapjack.Test.StackRawCallSeqStandardParity
