import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

/-!
# `data_to_word` configuration

The `gc_kind` and `config` datatypes and the pointer-layout helpers of
`cakeml/compiler/backend/data_to_wordScript.sml` that the word-level garbage
collector (`word_gcFunctions`) and `stack_alloc` use. HOL `bytes_in_word` is
`wordSemBytesInWord`.
-/

namespace Flapjack.Compiler.Backend.DataToWord

open Flapjack.WordSemStateFiniteExact

/-- Exact HOL `data_to_word$gc_kind` (`data_to_wordScript.sml:17-23`): no GC, the
simple copying GC, or a generational GC with generation sizes, smallest first. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "gc_kind"]
inductive GcKind where
  | none
  | simple
  | generational (sizes : List Nat)
  deriving DecidableEq, Repr

/-- Exact HOL `data_to_word$config` (`data_to_wordScript.sml:25-36`), field for
field in HOL order. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

structure Config where
  tagBits : Nat
  lenBits : Nat
  padBits : Nat
  lenSize : Nat
  hasDiv : Bool
  hasLongdiv : Bool
  be : Bool
  callEmptyFfi : Bool
  gcKind : GcKind
  deriving DecidableEq, Repr

/-- Exact HOL `small_shift_length_def` (`data_to_wordScript.sml:101-103`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def smallShiftLength (conf : Config) : Nat := conf.lenBits + conf.tagBits + 1

/-- Exact HOL `shift_length_def` (`data_to_wordScript.sml:105-107`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shiftLength (conf : Config) : Nat := 1 + conf.padBits + conf.lenBits + conf.tagBits + 1

/-- Exact HOL `get_gen_size_def` (`data_to_wordScript.sml:1109-1115`): the first
generation size in bytes, or `bytes_in_word * -1w` when absent or overflowing. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "get_gen_size_def"
  (words_as_type_indexed_bitvec)]
def getGenSize {width : Nat} [NeZero width] : List Nat → BitVec width
  | [] => wordSemBytesInWord * (-1)
  | x :: _ =>
      if (wordSemBytesInWord : BitVec width).toNat * x < 2 ^ width then
        wordSemBytesInWord * BitVec.ofNat width x
      else wordSemBytesInWord * (-1)

end Flapjack.Compiler.Backend.DataToWord
