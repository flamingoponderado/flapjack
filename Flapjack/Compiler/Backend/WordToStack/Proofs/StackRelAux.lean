import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstraction
import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexList
import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Misc.ListEl

namespace Flapjack.WordToStackProofs
open Flapjack.StackSem

/-- Inhabitation of the original nonempty frame carrier, for total HOL EL;
this witness does not choose the unspecified empty-list result. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Full four-clause original auxiliary relation, retaining independent source
frame, handler location and saved-handler word dimensions. Total HOL EL is
used even when the target-length guard supplies no source index bound.
Nat first-match lookup implements ALOOKUP; optional indexing implements LLOOKUP;
getD implements misc the; drop(length-n) implements LASTN_DROP_UNCOND, including
oversized n. No extra range, success, or representation premise is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_aux_def"
  (words_as_type_indexed_bitvec)]
noncomputable def stackRelAux {locWidth width frameWidth : Nat} [NeZero locWidth] [NeZero width] [NeZero frameWidth] (k len : Nat)
    (sourceStack : List (WordSemStackFrame frameWidth))
    (stack : List (Option (WordLocW locWidth × WordLocW width) × List Bool × List (WordLocW frameWidth))) :
    Prop :=
  match sourceStack, stack with
  | [], [] => True
  | .stackFrame n l0 l none :: xs, (none, bits, frame) :: rest =>
      (∀ n' v, l0.lookup n' = some v → l.lookup n' = none →
          adjustNames n' < k + bits.length ∧
          bits[k + bits.length - (adjustNames n' + 1)]? = some false ∧
          (indexList frame k).lookup (n' / 2) = some v) ∧
      filterBitmap bits (indexList frame k) = some (l.map (fun p => (adjustNames p.1, p.2)), []) ∧
      n.getD (frame.length + 1) = frame.length + 1 ∧
      stackRelAux k len xs rest
  | .stackFrame n l0 l (some (h1, l1, l2)) :: xs, (some (loc, hv), bits, frame) :: rest =>
      (h1 < rest.length →
          isHandlerFrame (Flapjack.holEl (rest.length - (h1 + 1)) xs) →
          hv = .word (BitVec.ofNat width (len - handlerVal (rest.drop (rest.length - (h1 + 1)))))) ∧
      loc = .loc l1 l2 ∧
      (∀ n' v, l0.lookup n' = some v → l.lookup n' = none →
          adjustNames n' < k + bits.length ∧
          bits[k + bits.length - (adjustNames n' + 1)]? = some false ∧
          (indexList frame k).lookup (n' / 2) = some v) ∧
      filterBitmap bits (indexList frame k) = some (l.map (fun p => (adjustNames p.1, p.2)), []) ∧
      n.getD (frame.length + 1) = frame.length + 1 ∧
      stackRelAux k len xs rest
  | _, _ => False

end Flapjack.WordToStackProofs
