import Flapjack.Compiler.Backend.Semantics.StackSem.StackCodec

/-! Kernel replay of26 original HOL rows in stacksem_stack_codec_probe.out.
The three captured type rows additionally show independent bitmap/stack widths.
These fixtures are finite coverage, not a universal cross-assistant theorem
or refinement of the Nat stack machine/full StackSem evaluator. -/
open Flapjack Flapjack.StackSem
private abbrev w (n : Nat) : WordLocW 8 := .word (BitVec.ofNat 8 n)
private abbrev l (block offset : Nat) : WordLocW 8 := .loc block offset

-- full_zero
example : fullReadBitmap ([13] : List (BitVec 8)) (w 0) = none := by decide +kernel
-- full_one
example : fullReadBitmap ([13] : List (BitVec 8)) (w 1) = some [true,false,true] := by decide +kernel
-- full_two
example : fullReadBitmap ([0,5] : List (BitVec 8)) (w 2) = some [true,false] := by decide +kernel
-- full_oob
example : fullReadBitmap ([13] : List (BitVec 8)) (w 2) = none := by decide +kernel
-- full_loc
example : fullReadBitmap ([13] : List (BitVec 8)) (l 1 0) = none := by decide +kernel
-- enc_empty
example : encStack ([] : List (BitVec 8)) ([] : List (WordLocW 8)) = none := by decide +kernel
-- enc_zero
example : encStack ([] : List (BitVec 8)) [w 0] = some [] := by decide +kernel
-- enc_zero_extra
example : encStack ([] : List (BitVec 8)) [w 0,w 0] = none := by decide +kernel
-- enc_loc
example : encStack ([3] : List (BitVec 8)) [l 1 0,w 0] = none := by decide +kernel
-- enc_true
example : encStack ([3] : List (BitVec 8)) [w 1,w 7,w 0] = some [w 7] := by decide +kernel
-- enc_false
example : encStack ([2] : List (BitVec 8)) [w 1,l 4 5,w 0] = some [] := by decide +kernel
-- enc_two
example : encStack ([3] : List (BitVec 8)) [w 1,w 7,w 1,l 4 0,w 0] = some [w 7,l 4 0] := by decide +kernel
-- enc_short
example : encStack ([3] : List (BitVec 8)) [w 1] = none := by decide +kernel
-- enc_missing_sentinel
example : encStack ([3] : List (BitVec 8)) [w 1,w 7] = none := by decide +kernel
-- enc_bad_continuation
example : encStack ([128] : List (BitVec 8)) [w 1,w 0] = none := by decide +kernel
-- dec_empty
example : decStack ([] : List (BitVec 8)) ([] : List (WordLocW 8)) [] = none := by decide +kernel
-- dec_zero
example : decStack ([] : List (BitVec 8)) [] [w 0] = some [w 0] := by decide +kernel
-- dec_true
example : decStack ([3] : List (BitVec 8)) [w 9] [w 1,w 7,w 0] = some [w 1,w 9,w 0] := by decide +kernel
-- dec_false
example : decStack ([2] : List (BitVec 8)) [] [w 1,l 4 5,w 0] = some [w 1,l 4 5,w 0] := by decide +kernel
-- dec_short_roots
example : decStack ([3] : List (BitVec 8)) [] [w 1,w 7,w 0] = none := by decide +kernel
-- dec_extra_roots
example : decStack ([3] : List (BitVec 8)) [w 9,w 10] [w 1,w 7,w 0] = none := by decide +kernel
-- dec_two
example : decStack ([3] : List (BitVec 8)) [w 9,l 2 1] [w 1,w 7,w 1,l 4 0,w 0] = some [w 1,w 9,w 1,l 2 1,w 0] := by decide +kernel
-- dec_zero_extra
example : decStack ([] : List (BitVec 8)) [] [w 0,w 1] = none := by decide +kernel
-- full_mixed
example : fullReadBitmap ([13] : List (BitVec 8)) (.word 1 : WordLocW 1) = some [true,false,true] := by decide +kernel
-- enc_mixed
example : encStack ([3] : List (BitVec 8)) ([.word 1,.word 1,.word 0] : List (WordLocW 1)) = some [.word 1] := by decide +kernel
-- dec_mixed
example : decStack ([3] : List (BitVec 8)) [.word 0] ([.word 1,.word 1,.word 0] : List (WordLocW 1)) = some [.word 1,.word 0,.word 0] := by decide +kernel
