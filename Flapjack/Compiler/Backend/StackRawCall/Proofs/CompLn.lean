import Flapjack.Compiler.Backend.StackRawCall
namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang
/-- Original full empty-info identity, retaining the unused source map binder. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_LN"
  (words_as_type_indexed_bitvec)]
theorem compLn {width : Nat} [NeZero width] (_info : Spt Nat) (body : HolProg width) :
    compTop .ln body = body ∧ comp .ln body = body := by
  induction body using comp.induct <;>
    simp_all [comp, compTop, compSeq, sptLookup]
  all_goals split <;> rfl
end Flapjack.Compiler.Backend.StackRawCall
