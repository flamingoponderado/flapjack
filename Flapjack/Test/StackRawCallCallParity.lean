import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call
namespace Flapjack.Test.StackRawCallCallParity
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemControl
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack.Compiler.Backend.StackRawCall.CallAssembly

example {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result :=
  compCorrectCall ret dest handler info source target post result induction hypothesis

example {width : Nat} [NeZero width] {C F : Type}
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result :=
  compCorrectCallReturn ret link l1 l2 dest handler info source target post result
    calleeIH returnIH exceptionIH hypothesis

example {C F : Type}
    (ret : Option (HolProg 1 × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg 1 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result :=
  compCorrectCall ret dest handler info source target post result induction hypothesis

example {C F : Type}
    (ret : HolProg 1) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 1 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 1 C F)
    (result : Option (StackSemResult 1))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result :=
  compCorrectCallReturn ret link l1 l2 dest handler info source target post result
    calleeIH returnIH exceptionIH hypothesis

example {C F : Type}
    (ret : Option (HolProg 8 × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg 8 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result :=
  compCorrectCall ret dest handler info source target post result induction hypothesis

example {C F : Type}
    (ret : HolProg 8) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 8 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 8 C F)
    (result : Option (StackSemResult 8))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result :=
  compCorrectCallReturn ret link l1 l2 dest handler info source target post result
    calleeIH returnIH exceptionIH hypothesis

example {C F : Type}
    (ret : Option (HolProg 64 × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result :=
  compCorrectCall ret dest handler info source target post result induction hypothesis

example {C F : Type}
    (ret : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 C F)
    (result : Option (StackSemResult 64))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result :=
  compCorrectCallReturn ret link l1 l2 dest handler info source target post result
    calleeIH returnIH exceptionIH hypothesis

example {C F : Type}
    (ret : Option (HolProg 80 × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg 80 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result :=
  compCorrectCall ret dest handler info source target post result induction hypothesis

example {C F : Type}
    (ret : HolProg 80) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 80 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 80 C F)
    (result : Option (StackSemResult 80))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result :=
  compCorrectCallReturn ret link l1 l2 dest handler info source target post result
    calleeIH returnIH exceptionIH hypothesis

example {width : Nat} [NeZero width] :
    comp (sptInsert 3 4 .ln)
      (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
        (.inl 3) none : HolProg width) =
      .call (some (.rawCall 3, 5, 7, 9)) (.inl 3) none := by
  simp [comp, compSeq, destCase, sptLookup_sptInsert_same]

example {width : Nat} [NeZero width] :
    comp (sptInsert 3 4 .ln)
      (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
        (.inr 6) (some (.seq (.stackFree 6) (.call none (.inl 3) none), 11, 13)) : HolProg width) =
      .call (some (.rawCall 3, 5, 7, 9)) (.inr 6)
        (some (.seq (.stackFree 2) (.rawCall 3), 11, 13)) := by
  simp [comp, compSeq, destCase, sptLookup_sptInsert_same]

#guard match comp (sptInsert 3 4 .ln)
    (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
      (.inl 3) none : HolProg 64) with
  | .call (some (.rawCall 3, 5, 7, 9)) (.inl 3) none => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
      (.inr 6) (some (.seq (.stackFree 6) (.call none (.inl 3) none), 11, 13)) : HolProg 64) with
  | .call (some (.rawCall 3, 5, 7, 9)) (.inr 6)
      (some (.seq (.stackFree 2) (.rawCall 3), 11, 13)) => true
  | _ => false
example (regs : HolFiniteMapExact Nat (WordLocW 64)) (code : Spt (HolProg 64)) :
    findCode (.inr 5) (regs.eraseEq 5) code = none := by
  simp [findCode, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
example : findCode (.inr 6)
    (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 64)).updateEq
      (6, .loc 3 0)).eraseEq 5) (sptInsert 3 (.skip : HolProg 64) .ln) = some .skip := by
  simp [findCode, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, sptLookup_sptInsert_same]

#guard match comp (sptInsert 3 4 .ln)
    (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
      (.inl 3) none : HolProg 80) with
  | .call (some (.rawCall 3, 5, 7, 9)) (.inl 3) none => true
  | _ => false
#guard match comp (sptInsert 3 4 .ln)
    (.call (some (.seq (.stackFree 4) (.call none (.inl 3) none), 5, 7, 9))
      (.inr 6) (some (.seq (.stackFree 6) (.call none (.inl 3) none), 11, 13)) : HolProg 80) with
  | .call (some (.rawCall 3, 5, 7, 9)) (.inr 6)
      (some (.seq (.stackFree 2) (.rawCall 3), 11, 13)) => true
  | _ => false
example (regs : HolFiniteMapExact Nat (WordLocW 80)) (code : Spt (HolProg 80)) :
    findCode (.inr 5) (regs.eraseEq 5) code = none := by
  simp [findCode, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
example : findCode (.inr 6)
    (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 80)).updateEq
      (6, .loc 3 0)).eraseEq 5) (sptInsert 3 (.skip : HolProg 80) .ln) = some .skip := by
  simp [findCode, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, sptLookup_sptInsert_same]

end Flapjack.Test.StackRawCallCallParity
