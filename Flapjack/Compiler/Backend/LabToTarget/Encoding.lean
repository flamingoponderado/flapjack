import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.LabToTarget.Native
import Flapjack.Compiler.Encoders.Asm

/-!
# Faithful Cake assembly encoding (`lab_to_target`)

Exact carriers and definitions from
`cakeml/compiler/backend/lab_to_targetScript.sml:15-61`.  The imported
`labLang` constructor-for-constructor carriers (`Lab`, `AsmWithLab`,
`AsmOrCbw`, `Line`, `Section`) are instantiated at HOL's actual carriers:
`HolAsm`, `HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm` and the opaque
`MlString`.  Only HOL's type-indexed `'a word` is translated to the
positive-width `BitVec width`; the `word8` byte lists keep their literal
fixed width.  The instruction encoder `enc` is a parameter of `enc_line`, as
in HOL, and is not the production assembler's encoder.

The other phase definitions live in sibling counterpart modules.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `lab_to_target$ffi_offset_def` (`lab_to_targetScript.sml:15-17`):
`ffi_offset = 16:num`.  A plain numeric constant, so no qualifier is needed. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "ffi_offset_def"]
def ffiOffset : Nat := 16

/-- Exact HOL `lab_to_target$lab_inst_def` (`lab_to_targetScript.sml:21-29`):
every labelled instruction becomes the corresponding unconditional `asm`
transfer through the supplied target word, with `Halt`, `Install` and
`CallFFI` all collapsing to `Jump`.  Only HOL's `'a word` is translated to
`BitVec width`; the `Lab` payloads are discarded exactly as in the source. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "lab_inst_def"
  (words_as_type_indexed_bitvec)]
def labInst {width : Nat} [NeZero width] (w : BitVec width)
    (instruction : AsmWithLab HolCmp (HolRegImm width) MlString) : HolAsm width :=
  match instruction with
  | .jump _ => .jump w
  | .jumpCmp c r ri _ => .jumpCmp c r ri w
  | .call _ => .call w
  | .locValue r _ => .loc r w
  | .halt => .jump w
  | .install => .jump w
  | .callFFI _ => .jump w

/-- Flapjack compatibility alias; the sole tagged implementation is
`cbwToAsmHOL` in the native counterpart module. -/
abbrev cbwToAsmExact := @cbwToAsmHOL

/-- Exact HOL `lab_to_target$enc_line_def` (`lab_to_targetScript.sml:40-47`):
a `Label` keeps its identity and takes the supplied `skip_len` as length; an
`Asm` re-encodes its `AsmOrCbw` through `enc ∘ cbw_to_asm` and records the
byte-list length; a `LabAsm` re-encodes `lab_inst 0w` at position `0w`.
The encoder `enc` is the HOL parameter, not the production assembler's
encoder. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_line_def"
  (words_as_type_indexed_bitvec)]
def encLine {width : Nat} [NeZero width] (enc : HolAsm width → List (BitVec 8))
    (skipLen : Nat)
    (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) :=
  match line with
  | .label n1 n2 _ => .label n1 n2 skipLen
  | .asm a _ _ =>
      let bs := enc (cbwToAsmExact a)
      .asm a bs bs.length
  | .labAsm l _ _ _ =>
      let bs := enc (labInst (0 : BitVec width) l)
      .labAsm l (0 : BitVec width) bs bs.length

/-- Exact HOL `lab_to_target$enc_sec_def` (`lab_to_targetScript.sml:49-52`):
`Section k xs` keeps its section id and maps `enc_line` over its lines. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_sec_def"
  (words_as_type_indexed_bitvec)]
def encSec {width : Nat} [NeZero width] (enc : HolAsm width → List (BitVec 8))
    (skipLen : Nat)
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :=
  ⟨sec.sectionId, sec.lines.map (encLine enc skipLen)⟩

/-- Exact HOL `lab_to_target$enc_sec_list_def` (`lab_to_targetScript.sml:54-57`):
`skip_len` is the length of the encoding of `Inst Skip`; each section is
encoded with that fixed length. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "enc_sec_list_def"
  (words_as_type_indexed_bitvec)]
def encSecList {width : Nat} [NeZero width] (enc : HolAsm width → List (BitVec 8))
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  let skipLen := (enc (.inst .skip)).length
  sections.map (encSec enc skipLen)

end Flapjack.Compiler.Backend.LabToTarget
