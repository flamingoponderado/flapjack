import Flapjack.Compiler.Backend.StackRawCall.Proofs.Labels
/-! Generic proof application and complete independent original label-set pairs. -/
namespace Flapjack.Test.StackRawCallLabelsParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.StackSem
example {width : Nat} [NeZero width] (info : Spt Nat) (body : HolProg width) :
    getLabelsExact (comp info body) = getLabelsExact body ∧
    getLabelsExact (compTop info body) = getLabelsExact body := getLabelsComp info body
private def tail : HolProg 64 := .seq (.stackFree 4) (.call none (.inl 7) none)
private def returning : HolProg 64 := .call (some (tail,2,3,4)) (.inl 9)
  (some (.loop tail,31,37))
private def tailHandler : HolProg 64 := .call none (.inl 9)
  (some (.call (some (.skip,2,3,4)) (.inl 9) none,31,37))
example : (getLabelsExact (comp (sptInsert 7 4 .ln) (.loop tail)),
    getLabelsExact (compTop (sptInsert 7 4 .ln) (.loop tail))) =
    ((fun _ => False), (fun _ => False)) := by
  apply Prod.ext <;> funext label <;>
    simp [comp, compTop, compSeq, destCase, tail, sptLookup, sptInsert, getLabelsExact]
example : (getLabelsExact (comp (sptInsert 7 2 .ln) (.loop tail)),
    getLabelsExact (compTop (sptInsert 7 2 .ln) (.loop tail))) =
    ((fun _ => False), (fun _ => False)) := by
  apply Prod.ext <;> funext label <;>
    simp [comp, compTop, compSeq, destCase, tail, sptLookup, sptInsert, getLabelsExact]
example : (getLabelsExact (comp (sptInsert 7 6 .ln) (.loop tail)),
    getLabelsExact (compTop (sptInsert 7 6 .ln) (.loop tail))) =
    ((fun _ => False), (fun _ => False)) := by
  apply Prod.ext <;> funext label <;>
    simp [comp, compTop, compSeq, destCase, tail, sptLookup, sptInsert, getLabelsExact]
example : (getLabelsExact (comp (sptInsert 7 4 .ln) returning),
    getLabelsExact (compTop (sptInsert 7 4 .ln) returning)) =
    ((fun label => label = (3,4) ∨ label = (31,37)),
      (fun label => label = (3,4) ∨ label = (31,37))) := by
  apply Prod.ext <;> funext label <;>
    simp [comp, compTop, compSeq, destCase, tail, returning, sptLookup, sptInsert, getLabelsExact]
example : (getLabelsExact (comp (sptInsert 7 4 .ln) tailHandler),
    getLabelsExact (compTop (sptInsert 7 4 .ln) tailHandler)) =
    ((fun _ => False), (fun _ => False)) := by
  apply Prod.ext <;> funext label <;> simp [comp, compTop, tailHandler, getLabelsExact]
#print axioms getLabelsComp
end Flapjack.Test.StackRawCallLabelsParity
