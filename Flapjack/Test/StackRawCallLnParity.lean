import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompLn
/-! Generic identity consumer and complete original paired-tree observations. -/
namespace Flapjack.Test.StackRawCallLnParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
example {width : Nat} [NeZero width] (info : Spt Nat) (body : HolProg width) :
    compTop .ln body = body ∧ comp .ln body = body := compLn info body
private def tail : HolProg 64 := .seq (.stackFree 4) (.call none (.inl 7) none)
private def loopZero : HolProg 64 := .loop (.seq (.stackFree 0) (.call none (.inl 9) none))
private def returning : HolProg 64 := .call (some (tail,2,3,4)) (.inr 9)
  (some (.loop tail,31,37))
private def tailHandler : HolProg 64 := .call none (.inl 9) (some (tail,31,37))
example : (compTop .ln tail, comp .ln tail) = (tail,tail) := by cbv
example : (compTop .ln loopZero, comp .ln loopZero) = (loopZero,loopZero) := by cbv
example : (compTop .ln returning, comp .ln returning) = (returning,returning) := by cbv
example : (compTop .ln tailHandler, comp .ln tailHandler) = (tailHandler,tailHandler) := by cbv
#print axioms compLn
end Flapjack.Test.StackRawCallLnParity
