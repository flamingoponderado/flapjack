import Flapjack.Compiler.Backend.LabLang
import Flapjack.Misc.Sptree
import Flapjack.Misc.FindIndex
import Flapjack.FfiHOL

/-!
# Faithful Lab-to-target position and offset helpers

Literal ports of the `lab_to_targetScript.sml` position helpers over the
faithful `LabLang` carriers. `find_pos`, `get_label` and `get_ffi_index` are
word-free; `get_jump_offset` builds width-indexed offsets.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang

/-- Exact HOL `ffi_offset_def` (`cakeml/compiler/backend/lab_to_targetScript.sml:15-16`). -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "ffi_offset_def"]
def ffiOffset : Nat := 16

/-- Exact HOL `find_pos_def` (`cakeml/compiler/backend/lab_to_targetScript.sml:86-89`):
    `find_pos (Lab k1 k2) labs = lookup_any k2 (lookup_any k1 labs LN) 0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "find_pos_def"]
def findPos (label : Lab) (labs : Spt (Spt Nat)) : Nat :=
  match label with
  | .lab sectionNumber label => lookupAny label (lookupAny sectionNumber labs .ln) 0

/-- Exact HOL `get_label_def` (`cakeml/compiler/backend/lab_to_targetScript.sml:91-97`):
    the label carried by a jump/call/loc-value, defaulting to `Lab 0 0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_label_def"]
def getLabel {Cmp RegImm MlString : Type} : AsmWithLab Cmp RegImm MlString → Lab
  | .jump target => target
  | .jumpCmp _ _ _ target => target
  | .call target => target
  | .locValue _ target => target
  | _ => .lab 0 0

/-- Exact HOL `get_ffi_index_def` (`cakeml/compiler/backend/lab_to_targetScript.sml:104-107`):
    `get_ffi_index ffis s = the 0 (find_index s ffis 0)`, i.e. the first index
    of `s` in `ffis` with default `0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_ffi_index_def"]
def getFfiIndex (ffis : List HolFfiName) (s : HolFfiName) : Nat :=
  (Flapjack.Misc.findIndex s ffis 0).getD 0

/-- Exact HOL `get_jump_offset_def` (`cakeml/compiler/backend/lab_to_targetScript.sml:109-118`):
    the relative back-offset from the current position to the target, with the
    special call-FFI/install/halt forms; `n2w` becomes `BitVec.ofNat width`.
    HOL fixes the `asm_with_lab` name payload to `mlstring`, so the name carrier
    is the native `MlString`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_jump_offset_def"
  (words_as_type_indexed_bitvec)]
def getJumpOffset {width : Nat} [NeZero width] {Cmp RegImm : Type}
    (instruction : AsmWithLab Cmp RegImm Flapjack.Basis.Pure.MlString.MlString)
    (ffis : List HolFfiName) (labs : Spt (Spt Nat)) (pos : Nat) : BitVec width :=
  match instruction with
  | .callFFI s =>
      (0 : BitVec width) - BitVec.ofNat width (pos + (3 + getFfiIndex ffis (.extCall s)) * ffiOffset)
  | .install =>
      (0 : BitVec width) - BitVec.ofNat width (pos + 2 * ffiOffset)
  | .halt =>
      (0 : BitVec width) - BitVec.ofNat width (pos + ffiOffset)
  | a => BitVec.ofNat width (findPos (getLabel a) labs) - BitVec.ofNat width pos

end Flapjack.Compiler.Backend.LabToTarget
