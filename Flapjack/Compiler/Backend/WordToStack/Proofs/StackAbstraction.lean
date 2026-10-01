import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

/-! Exact target-stack abstraction used by Word-to-Stack stack_rel. -/
namespace Flapjack.WordToStackProofs

/-- Literal source abstraction. Frame-size predictions and saved source locals
are intentionally ignored here; the later stack relation checks consistency.
The bitmap words have an independent positive dimension from the stack/frame
`word_loc` words, as in the source (`full_read_bitmap` is polymorphic in the
bitmap word type and the `word_loc` type). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_def"
  (words_as_type_indexed_bitvec)]
def absStack {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth))
    (frames : List (WordSemStackFrame width)) (stack : List (WordLocW width))
    (lens : List Nat) :
    Option (List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width))) :=
  match frames, stack, lens with
  | [], stack, [] => if stack = [.word 0] then some [] else none
  | .stackFrame _ _ _ none :: xs, w :: stack, len :: lens =>
      match StackSem.fullReadBitmap bitmaps w with
      | none => none
      | some bits =>
          if bits.length ≠ len then none else
          if stack.length < len then none else
          let frame := stack.take len
          let rest := stack.drop len
          match absStack bitmaps xs rest lens with
          | none => none
          | some ys => some ((none, bits, frame) :: ys)
  | .stackFrame _ _ _ (some _) :: xs, w :: stack, len :: lens =>
      if w ≠ .word 1 then none else
      match stack with
      | loc :: hv :: w :: stack =>
          match StackSem.fullReadBitmap bitmaps w with
          | none => none
          | some bits =>
              if bits.length ≠ len then none else
              if stack.length < len then none else
              let frame := stack.take len
              let rest := stack.drop len
              match absStack bitmaps xs rest lens with
              | none => none
              | some ys => some ((some (loc, hv), bits, frame) :: ys)
      | _ => none
  | _, _, _ => none
termination_by frames

end Flapjack.WordToStackProofs
