import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq
namespace Flapjack.Test.StackRawCallSeqParity
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
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result :=
  compCorrectSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 1) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result :=
  compCorrectSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 8) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result :=
  compCorrectSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 64) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result :=
  compCorrectSeq first second info source target post result firstIH secondIH hypothesis

example {C F : Type}
    (first second : HolProg 80) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result :=
  compCorrectSeq first second info source target post result firstIH secondIH hypothesis

example {width : Nat} [NeZero width] :
    comp (sptInsert 3 4 .ln)
      (.seq (.stackFree 4) (.call none (.inl 3) none) : HolProg width) =
      .rawCall 3 := by
  simp [comp, compSeq, destCase, sptLookup_sptInsert_same]

#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 4) (.call none (.inl 3) none) : HolProg 64) with
  | .rawCall 3 => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 4) (.call none (.inl 3) none) : HolProg 80) with
  | .rawCall 3 => true
  | _ => false
example {width : Nat} [NeZero width] :
    comp (sptInsert 3 4 .ln)
      (.seq (.stackFree 6) (.call none (.inl 3) none) : HolProg width) =
      .seq (.stackFree 2) (.rawCall 3) := by
  simp [comp, compSeq, destCase, sptLookup_sptInsert_same]

#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 6) (.call none (.inl 3) none) : HolProg 64) with
  | .seq (.stackFree 2) (.rawCall 3) => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 6) (.call none (.inl 3) none) : HolProg 80) with
  | .seq (.stackFree 2) (.rawCall 3) => true
  | _ => false
example {width : Nat} [NeZero width] :
    comp (sptInsert 3 4 .ln)
      (.seq (.stackFree 2) (.call none (.inl 3) none) : HolProg width) =
      .seq .tick (.seq (.stackAlloc 2) (.rawCall 3)) := by
  simp [comp, compSeq, destCase, sptLookup_sptInsert_same]

#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 2) (.call none (.inl 3) none) : HolProg 64) with
  | .seq .tick (.seq (.stackAlloc 2) (.rawCall 3)) => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.seq (.stackFree 2) (.call none (.inl 3) none) : HolProg 80) with
  | .seq .tick (.seq (.stackAlloc 2) (.rawCall 3)) => true
  | _ => false

end Flapjack.Test.StackRawCallSeqParity
