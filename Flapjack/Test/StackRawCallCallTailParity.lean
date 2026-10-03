import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail
namespace Flapjack.Test.StackRawCallCallTailParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase

example {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result :=
  compCorrectCallTail dest handler info source target post result calleeIH hypothesis

example {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg 1 × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result :=
  compCorrectCallTail dest handler info source target post result calleeIH hypothesis

example {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg 8 × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result :=
  compCorrectCallTail dest handler info source target post result calleeIH hypothesis

example {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result :=
  compCorrectCallTail dest handler info source target post result calleeIH hypothesis

example {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg 80 × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call none dest handler)) info target post result ∧
    SimulationResult (comp info (.call none dest handler)) info target post result :=
  compCorrectCallTail dest handler info source target post result calleeIH hypothesis

example {width : Nat} [NeZero width] (info : Spt Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) :
    comp info (.call none dest handler) = .call none dest handler := by
  cases handler <;> rfl

#guard match comp (sptInsert 3 4 .ln)
    (.call none (.inl 3) none : HolProg 64) with
  | .call none (.inl 3) none => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.call none (.inr 5) (some (.seq (.stackFree 4) (.call none (.inl 3) none), 7, 9)) : HolProg 64) with
  | .call none (.inr 5) (some (.seq (.stackFree 4) (.call none (.inl 3) none), 7, 9)) => true
  | _ => false

#guard match comp (sptInsert 3 4 .ln)
    (.call none (.inl 3) none : HolProg 80) with
  | .call none (.inl 3) none => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.call none (.inr 5) (some (.seq (.stackFree 4) (.call none (.inl 3) none), 7, 9)) : HolProg 80) with
  | .call none (.inr 5) (some (.seq (.stackFree 4) (.call none (.inl 3) none), 7, 9)) => true
  | _ => false

end Flapjack.Test.StackRawCallCallTailParity
