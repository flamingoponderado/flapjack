import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Original frame-info relation: each recorded size is witnessed by the
literal first Seq allocation in the original code, including zero sizes.
The code/info carriers are HOL tree maps, not finite-support function maps. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "state_ok_def"
  (words_as_type_indexed_bitvec)]
def stateOk {width : Nat} [NeZero width] (info : Spt Nat)
    (code : Spt (HolProg width)) : Prop :=
  ∀ n v, sptLookup n info = some v →
    ∃ body, sptLookup n code = some (.seq (.stackAlloc v) body)

/-- Flapjack infrastructure: empty info imposes no frame requirements.
This is a direct consequence of the original relation, not a separate HOL theorem. -/
theorem stateOk_empty {width : Nat} [NeZero width] (code : Spt (HolProg width)) :
    stateOk .ln code := by
  intro n v h
  simp [sptLookup] at h

end Flapjack.Compiler.Backend.StackRawCall
