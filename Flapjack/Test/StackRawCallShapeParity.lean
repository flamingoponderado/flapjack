import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape

/-! Source theorem application and independent original branch observations.
No fixture or consumer assumes the shape conclusion. -/
namespace Flapjack.Test.StackRawCallShapeParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
example {width : Nat} [NeZero width] (a b fallback : HolProg width) (info : Spt Nat)
    (h : compSeq a b info fallback ≠ fallback) :
    ∃ k dest, a = .stackFree k ∧ b = .call none (.inl dest) none :=
  compSeqNeqImp a b fallback info h
example : compSeq (.stackFree 4) (.call none (.inl 7) none)
    (sptInsert 7 4 .ln) (.skip : HolProg 64) ≠ .skip := by cbv; intro h; cases h
example : compSeq (.stackFree 4) (.call none (.inl 7) none)
    (sptInsert 7 2 .ln) (.skip : HolProg 64) ≠ .skip := by cbv; intro h; cases h
example : compSeq (.stackFree 4) (.call none (.inl 7) none)
    (sptInsert 7 6 .ln) (.skip : HolProg 64) ≠ .skip := by cbv; intro h; cases h
example : compSeq (.stackFree 4) (.call none (.inl 7) none)
    .ln (.skip : HolProg 64) = .skip := by cbv
example : compSeq (.stackFree 4) (.call none (.inl 7) (some (.skip,3,4)))
    (sptInsert 7 4 .ln) (.skip : HolProg 64) = .skip := by cbv
#print axioms compSeqNeqImp
end Flapjack.Test.StackRawCallShapeParity
