module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.State

@[expose] public section

/-! Architecture and heap-limit invariant for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Data limits agree with the word-language architecture, stack limit, heap
length and floating-point features, with the source's non-overflow bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "limits_inv_def"
  (words_as_type_indexed_bitvec)]
def limitsInv {width : Nat} [NeZero width] (limits : DataSem.Limits)
    (heapLength : Option (WordLocW width)) (stackLimit lengthSize : Nat)
    (hasFpOps hasFpTern : Bool) : Prop :=
  let bytesInWord := BitVec.ofNat width (width / 8)
  limits.stackLimit = stackLimit ∧
  limits.lengthLimit = lengthSize ∧
  limits.arch64Bit = decide (width = 64) ∧
  heapLength = some (.word (bytesInWord * BitVec.ofNat width limits.heapLimit)) ∧
  limits.heapLimit * bytesInWord.toNat < 2 ^ width ∧
  limits.hasFpOps = hasFpOps ∧
  limits.hasFpTops = hasFpTern

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
