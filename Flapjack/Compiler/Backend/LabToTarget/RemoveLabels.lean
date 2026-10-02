import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Padding
import Flapjack.Compiler.Backend.LabToTarget.SecondPass
import Flapjack.Compiler.Encoders.Asm
import Flapjack.FfiHOL
import Flapjack.Misc.Sptree
import Flapjack.Basis.Pure.MlString

/-!
# Faithful Cake zero-label accumulation and label-removal loop (`lab_to_target`)

Exact definitions from `cakeml/compiler/backend/lab_to_targetScript.sml:248-337`.
`zero_labs_acc_of` collects the labels whose second component is zero from an
`asm_with_lab`; `line_get_zero_labs_acc` extracts the instruction from a
`LabAsm`, `sec_get_zero_labs_acc` and `get_zero_labs_acc` fold it over a
section's lines and a program's sections, and `zero_labs_acc_exist` checks that
each collected label is present in the computed label map with a live offset
zero entry.  `remove_labels_loop` computes labels, re-runs the second pass to
update non-label encodings, re-derives the labels after adjusting label
lengths, pads the labels into instructions, and succeeds only when the pass
stayed consistent, every section is light-valid and every zero label exists.
`remove_labels` seeds that loop by encoding the program.  `line_bytes` projects
the encoded bytes of a line and `prog_to_bytes` flattens a program to bytes.

HOL `line` and `sec` share a single type-indexed word parameter `'a`, so the
imported LabLang carriers are instantiated at HOL's actual carriers: `HolAsm`,
`HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm` and the opaque `MlString`, with
only HOL's `'a word` translated to the positive-width `BitVec width`.  HOL
`insert` is `sptInsert`, `LN` is `.ln`, `lookup` is `sptLookup`, `toAList` is
`sptToAList`, `EVERY` is `List.all`, `FOLDR` is `List.foldr`, and `T`/`F` are
`true`/`false`.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack

/-- Exact HOL `lab_to_target$zero_labs_acc_of_def`
(`lab_to_targetScript.sml:248-256`, `[simp]`), clause for clause: `LocValue`,
`Jump` and `JumpCmp` whose target is `Lab n1 n2` insert `n1` when `n2 = 0` and
otherwise leave the accumulator unchanged; every other instruction is a
catch-all returning the accumulator. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "zero_labs_acc_of_def"
  (words_as_type_indexed_bitvec)]
def zeroLabsAccOf {width : Nat} [NeZero width] :
    AsmWithLab HolCmp (HolRegImm width) MlString → NumSet → NumSet
  | .locValue _ (.lab n1 n2), acc => if n2 = 0 then sptInsert n1 () acc else acc
  | .jump (.lab n1 n2), acc => if n2 = 0 then sptInsert n1 () acc else acc
  | .jumpCmp _ _ _ (.lab n1 n2), acc =>
      if n2 = 0 then sptInsert n1 () acc else acc
  | _, acc => acc

/-- Exact HOL `lab_to_target$line_get_zero_labs_acc_def`
(`lab_to_targetScript.sml:259-262`), clause for clause: a `LabAsm a _ _ _`
delegates to `zero_labs_acc_of a`, any other line returns the accumulator. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "line_get_zero_labs_acc_def"
  (words_as_type_indexed_bitvec)]
def lineGetZeroLabsAcc {width : Nat} [NeZero width] :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → NumSet → NumSet
  | .labAsm a _ _ _, acc => zeroLabsAccOf a acc
  | _, acc => acc

/-- Exact HOL `lab_to_target$sec_get_zero_labs_acc_def`
(`lab_to_targetScript.sml:264-267`): `Section _ lines` folds
`line_get_zero_labs_acc` over its lines with `FOLDR` (Lean `List.foldr`). -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_get_zero_labs_acc_def"
  (words_as_type_indexed_bitvec)]
def secGetZeroLabsAcc {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (acc : NumSet) :
    NumSet :=
  sec.lines.foldr lineGetZeroLabsAcc acc

/-- Exact HOL `lab_to_target$get_zero_labs_acc_def`
(`lab_to_targetScript.sml:269-272`): fold `sec_get_zero_labs_acc` over the
sections starting from the empty set `LN`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_zero_labs_acc_def"
  (words_as_type_indexed_bitvec)]
def getZeroLabsAcc {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : NumSet :=
  code.foldr secGetZeroLabsAcc .ln

/-- Exact HOL `lab_to_target$zero_labs_acc_exist_def`
(`lab_to_targetScript.sml:274-282`): for every `(n, _)` of `toAList` of the
collected zero labels, the label map `labs` must hold `n` (`F` when absent) and
its inner map must hold key `0` (`lookup 0 l ≠ NONE`, rendered as
`(sptLookup 0 l).isSome`). -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "zero_labs_acc_exist_def"
  (words_as_type_indexed_bitvec)]
def zeroLabsAccExist {width : Nat} [NeZero width] {α : Type} (labs : Spt (Spt α))
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Bool :=
  (sptToAList (getZeroLabsAcc code)).all (fun p =>
    match sptLookup p.1 labs with
    | none => false
    | some l => (sptLookup 0 l).isSome)

/-- Exact HOL `lab_to_target$all_enc_ok_light` (`lab_to_targetScript.sml:188`,
declared as an `Overload`, which the reference checker resolves as a
declaration): `all_enc_ok_light c ls = EVERY (sec_ok_light c) ls`, rendered as
`List.all` over the same exact `secOkLight`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "all_enc_ok_light"
  (words_as_type_indexed_bitvec)]
def allEncOkLight {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Bool :=
  sections.all (secOkLight config)

/-- Exact HOL `lab_to_target$remove_labels_loop_def`
(`lab_to_targetScript.sml:286-311`), clause for clause.  It computes
`labs = compute_labels_alt pos sec_list init_labs`, runs
`enc_secs_again pos labs ffis c.encode sec_list` (shadowing `sec_list`), and
when the pass is consistent (`done`) adjusts label lengths with
`upd_lab_len pos`, recomputes the labels, re-runs `enc_secs_again` on the
result, pads with `pad_code (c.encode (Inst Skip))`, and returns
`SOME (sec_list, labs)` only when `done /\ all_enc_ok_light c sec_list /\
zero_labs_acc_exist labs sec_list`; otherwise it retries with the clock
decremented, or returns `NONE` at clock `0`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "remove_labels_loop_def"
  (words_as_type_indexed_bitvec)]
def removeLabelsLoop {width : Nat} [NeZero width] (clock : Nat)
    (config : AsmConfigExact width) (pos : Nat) (initLabs : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) × Spt (Spt Nat)) :=
  let labs := computeLabelsAlt pos secList initLabs
  let (secList, done) := encSecsAgain pos labs ffis config.encode secList
  if done then
    let secList := updLabLen pos secList
    let labs := computeLabelsAlt pos secList initLabs
    let (secList, done) := encSecsAgain pos labs ffis config.encode secList
    let secList := padCode (config.encode (.inst .skip)) secList
    if done && allEncOkLight config secList && zeroLabsAccExist labs secList then
      some (secList, labs)
    else none
  else
    if clock = 0 then none
    else removeLabelsLoop (clock - 1) config pos initLabs ffis secList
termination_by clock

/-- Exact HOL `lab_to_target$remove_labels_def`
(`lab_to_targetScript.sml:313-322`): `remove_labels init_clock c pos labs ffis
sec_list = remove_labels_loop init_clock c pos labs ffis
(enc_sec_list c.encode sec_list)`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "remove_labels_def"
  (words_as_type_indexed_bitvec)]
def removeLabels {width : Nat} [NeZero width] (initClock : Nat)
    (config : AsmConfigExact width) (pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName)
    (secList : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    Option (List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) × Spt (Spt Nat)) :=
  removeLabelsLoop initClock config pos labs ffis (encSecList config.encode secList)

/-- Exact HOL `lab_to_target$line_bytes_def` (`lab_to_targetScript.sml:326-330`):
a `Label` has no bytes; `Asm` and `LabAsm` return their recorded byte list. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "line_bytes_def"
  (words_as_type_indexed_bitvec)]
def lineBytes {width : Nat} [NeZero width] :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → List (BitVec 8)
  | .label _ _ _ => []
  | .asm _ bytes _ => bytes
  | .labAsm _ _ bytes _ => bytes

/-- Exact HOL `lab_to_target$prog_to_bytes_def` (`lab_to_targetScript.sml:332-337`),
all three clauses: `[]` is `[]`; a section with no lines is skipped by
recursing on the rest; a section with a first line `y` emits `line_bytes y`
followed by the flattening of the same section with `y` removed. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "prog_to_bytes_def"
  (words_as_type_indexed_bitvec)]
def progToBytes {width : Nat} [NeZero width] :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → List (BitVec 8)
  | [] => []
  | ⟨_, []⟩ :: xs => progToBytes xs
  | ⟨k, y :: ys⟩ :: xs => lineBytes y ++ progToBytes (⟨k, ys⟩ :: xs)

end Flapjack.Compiler.Backend.LabToTarget
