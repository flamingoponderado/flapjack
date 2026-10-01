import Flapjack.Misc.LookupAny
import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Labels
import Flapjack.Compiler.Encoders.Asm
import Flapjack.FfiHOL
import Flapjack.Misc.FindIndex
import Flapjack.Misc.Sptree

/-!
# Faithful Cake position and jump-offset lookups (`lab_to_target`)

Exact carriers-witnessed definitions from
`cakeml/compiler/backend/lab_to_targetScript.sml:86-118`.  `find_pos` resolves a
two-level `spt` label map to a byte position with a `0` default; `get_label`
projects the target label of a labelled instruction, defaulting to `Lab 0 0`;
`get_ffi_index` is HOL's generic `find_index` with a `0` default; and
`get_jump_offset` computes the target-relative jump offset for the four
instruction classes, using the running section position `pos : num` and the
`ffiname list` discovered by `find_ffi_names`.

Only HOL's type-indexed `'a word` is translated to `BitVec width`.  HOL's
`denum` position (`pos`) is a plain `num`, so it is Lean `Nat`, and the
external-call names are the exact `HolFfiName` carrier (`ffiScript.sml:27-29`).
HOL `lookup_any`, `find_index` and `the` are the reviewed `lookupAny`,
`findIndex` and `Option.getD`; equality of the generic FFI-name element type is
rendered by the standard `DecidableEq` instance.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack
open Flapjack.Misc

/-- Exact HOL `lab_to_target$find_pos_def` (`lab_to_targetScript.sml:86-89`):
`find_pos (Lab k1 k2) labs = lookup_any k2 (lookup_any k1 labs LN) 0 : num`.
The outer lookup default is the empty inner `spt`; the inner lookup default is
the numeric position `0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "find_pos_def"]
def findPos : Lab → Spt (Spt Nat) → Nat
  | .lab sectionNumber label, labs => lookupAny label (lookupAny sectionNumber labs .ln) 0

/-- Exact HOL `lab_to_target$get_label_def` (`lab_to_targetScript.sml:91-98`):
the target label of `Jump`, `JumpCmp`, `Call` and `LocValue`; every other
labelled instruction (`CallFFI`, `Install`, `Halt`) returns the impossible
`Lab 0 0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_label_def"
  (words_as_type_indexed_bitvec)]
def getLabel {width : Nat} [NeZero width] :
    AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString → Lab
  | .jump l => l
  | .jumpCmp _ _ _ l => l
  | .call l => l
  | .locValue _ l => l
  | _ => .lab 0 0

/-- Exact HOL `lab_to_target$get_ffi_index_def` (`lab_to_targetScript.sml:104-107`):
`get_ffi_index ffis s = the 0 (find_index s ffis 0)`.  HOL `=` on the generic
element type is the standard decidable equality. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_ffi_index_def"]
def getFfiIndex {α : Type} [DecidableEq α] (ffis : List α) (s : α) : Nat :=
  (findIndex s ffis 0).getD 0

/-- Exact HOL `lab_to_target$get_jump_offset_def`
(`lab_to_targetScript.sml:109-118`): `CallFFI`, `Install` and `Halt` get the
fixed negative offsets `0w - n2w (pos + (3 + index) * ffi_offset)`,
`0w - n2w (pos + 2 * ffi_offset)` and `0w - n2w (pos + ffi_offset)`; every other
instruction jumps to its looked-up label, `n2w (find_pos (get_label a) labs) -
n2w pos`.  The `0w -` subtraction and `n2w` rendering are kept literal.

HOL's result word dimension is independent of the instruction's `reg_imm` word
dimension: the returned `'b word` is constrained by nothing in the body other
than `n2w : num -> 'b word`.  The two maintain separate positive-width binders,
so the generic definition is preserved rather than specialized. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_jump_offset_def"
  (words_as_type_indexed_bitvec)]
def getJumpOffset {regImmWidth : Nat} {width : Nat} [NeZero regImmWidth] [NeZero width]
    (a : AsmWithLab HolCmp (HolRegImm regImmWidth)
      Flapjack.Basis.Pure.MlString.MlString)
    (ffis : List HolFfiName) (labs : Spt (Spt Nat)) (pos : Nat) : BitVec width :=
  match a with
  | .callFFI s =>
      0 - BitVec.ofNat width
        (pos + (3 + getFfiIndex ffis (.extCall s)) * ffiOffset)
  | .install => 0 - BitVec.ofNat width (pos + 2 * ffiOffset)
  | .halt => 0 - BitVec.ofNat width (pos + ffiOffset)
  | a => BitVec.ofNat width (findPos (getLabel a) labs) - BitVec.ofNat width pos

end Flapjack.Compiler.Backend.LabToTarget
