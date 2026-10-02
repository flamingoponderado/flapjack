import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSem
/-- Original full label-set preservation for recursive and top compilation.
There is no validity, evaluation or successful lookup premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "get_labels_comp"
  (words_as_type_indexed_bitvec)]
theorem getLabelsComp {width : Nat} [NeZero width] (info : Spt Nat) (body : HolProg width) :
    getLabelsExact (comp info body) = getLabelsExact body ∧
    getLabelsExact (compTop info body) = getLabelsExact body := by
  induction body using comp.induct with
  | case1 first second ihFirst ihSecond =>
    constructor
    · by_cases h : compSeq first second info (.seq (comp info first) (comp info second)) =
          .seq (comp info first) (comp info second)
      · simp [comp, h, getLabelsExact, ihFirst.1, ihSecond.1]
      · obtain ⟨k, dest, rfl, rfl⟩ := compSeqNeqImp first second
          (.seq (comp info first) (comp info second)) info h
        simp only [comp, compSeq, destCase]
        split <;> try simp_all [getLabelsExact]
        all_goals split <;> try simp_all [getLabelsExact]
        all_goals split <;> try simp_all [getLabelsExact]
    · simp [compTop, getLabelsExact, ihFirst.1, ihSecond.1]
  | _ => simp_all [comp, compTop, getLabelsExact]
end Flapjack.Compiler.Backend.StackRawCall
