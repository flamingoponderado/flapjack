import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect

namespace Flapjack.Test.StackRawCallCompCorrectParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall

example {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (compTop info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (comp info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) :=
  FullCompCorrect.compCorrect program source target info result post hypothesis

example {C F : Type}
    (program : HolProg 1) (source target : StackSemStateFiniteExact 1 C F)
    (info : Spt Nat) (result : Option (StackSemResult 1))
    (post : StackSemStateFiniteExact 1 C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (compTop info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 1 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (comp info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 1 2))) →
        stackSpace = targetState.stackSpace)) :=
  FullCompCorrect.compCorrect program source target info result post hypothesis

example {C F : Type}
    (program : HolProg 8) (source target : StackSemStateFiniteExact 8 C F)
    (info : Spt Nat) (result : Option (StackSemResult 8))
    (post : StackSemStateFiniteExact 8 C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (compTop info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 8 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (comp info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 8 2))) →
        stackSpace = targetState.stackSpace)) :=
  FullCompCorrect.compCorrect program source target info result post hypothesis

example {C F : Type}
    (program : HolProg 64) (source target : StackSemStateFiniteExact 64 C F)
    (info : Spt Nat) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (compTop info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 64 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (comp info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 64 2))) →
        stackSpace = targetState.stackSpace)) :=
  FullCompCorrect.compCorrect program source target info result post hypothesis

example {C F : Type}
    (program : HolProg 80) (source target : StackSemStateFiniteExact 80 C F)
    (info : Spt Nat) (result : Option (StackSemResult 80))
    (post : StackSemStateFiniteExact 80 C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (compTop info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 80 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      stateRel info post targetState ∧
      StackSemEvaluate.evaluate (comp info program,
        {target with clock := target.clock + clock}) =
        (result, {targetState with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat 80 2))) →
        stackSpace = targetState.stackSpace)) :=
  FullCompCorrect.compCorrect program source target info result post hypothesis

end Flapjack.Test.StackRawCallCompCorrectParity
