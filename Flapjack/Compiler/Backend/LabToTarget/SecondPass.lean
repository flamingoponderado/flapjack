import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Positions
import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.Sptree
import Flapjack.Basis.Pure.MlString

/-!
# Faithful Cake second-pass assembly rewriting (`lab_to_target`)

Exact definitions from `cakeml/compiler/backend/lab_to_targetScript.sml:120-166`.
`enc_lines_again` walks a section's lines carrying a running byte position `pos`,
an accumulator `acc` and a success flag `ok`; a `Label` or `Asm` advances `pos`
by its recorded length, while a `LabAsm` recomputes its jump offset with
`get_jump_offset` and, when it changed, re-encodes the rewritten instruction
through the supplied encoder `enc`, taking the larger of the new encoding length
and the old length and conjoining `ok` with `l1 = l`.  `enc_secs_again` maps that
over a program's sections threading the position and conjoining each section's
flag.  `lines_upd_lab_len` rewrites every label length to `0`/`1` according to
the parity of the running position, and `upd_lab_len` maps that over sections.

HOL `line` and `sec` share a single type-indexed word parameter `'a`, so the
imported LabLang carriers are instantiated at HOL's actual carriers: `HolAsm`,
`HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm` and the opaque `MlString`, with
only HOL's `'a word` translated to the positive-width `BitVec width`.  HOL
`REVERSE` is `List.reverse`, `MAX` is `Nat.max`, `LENGTH` is `.length`, `EVEN`
is `pos % 2 = 0`, and `T`/`/\` are `true`/`&&` on `Bool`.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack

/-- Exact HOL `lab_to_target$enc_lines_again_def`
(`lab_to_targetScript.sml:120-136`), clause for clause.  `[]` returns the
reversed accumulator, the final position and the flag; `Label`/`Asm` advance the
position by their length; `LabAsm a w bytes l` recomputes `w1 = get_jump_offset
a ffis labs pos`, keeps the line when `w = w1`, and otherwise re-encodes
`lab_inst w1 a` and replaces the line by `LabAsm a w1 bs (MAX (LENGTH bs) l)`,
conjoining `ok` with `l1 = l`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def encLinesAgain {width : Nat} [NeZero width] (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (enc : HolAsm width → List (BitVec 8))
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (ok : Bool) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) × Nat × Bool :=
  match lines with
  | [] => (acc.reverse, pos, ok)
  | .label k1 k2 l :: xs =>
      encLinesAgain labs ffis (pos + l) enc xs (.label k1 k2 l :: acc) ok
  | .asm x1 x2 l :: xs =>
      encLinesAgain labs ffis (pos + l) enc xs (.asm x1 x2 l :: acc) ok
  | .labAsm a w bytes l :: xs =>
      let w1 := getJumpOffset a ffis labs pos
      if w = w1 then
        encLinesAgain labs ffis (pos + l) enc xs (.labAsm a w bytes l :: acc) ok
      else
        let bs := enc (labInst w1 a)
        let l1 := max bs.length l
        encLinesAgain labs ffis (pos + l1) enc xs
          (.labAsm a w1 bs l1 :: acc) (ok && decide (l1 = l))

/-- Exact HOL `lab_to_target$enc_secs_again_def`
(`lab_to_targetScript.sml:137-144`), clause for clause.  `[]` is `([], T)`; each
`Section s lines` is rewritten by `enc_lines_again` seeded with `([], T)` from
the running position, and the remainder from the resulting position, conjoining
the two flags. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def encSecsAgain {width : Nat} [NeZero width] (pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (enc : HolAsm width → List (BitVec 8))
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) × Bool :=
  match sections with
  | [] => ([], true)
  | ⟨s, lines⟩ :: rest =>
      let (lines1, pos1, ok) := encLinesAgain labs ffis pos enc lines [] true
      let (rest1, ok1) := encSecsAgain pos1 labs ffis enc rest
      (⟨s, lines1⟩ :: rest1, ok && ok1)

/-- Exact HOL `lab_to_target$lines_upd_lab_len_def`
(`lab_to_targetScript.sml:147-157`), clause for clause.  `[]` returns the
reversed accumulator and the final position; a `Label` is rewritten to length
`l1 = if EVEN pos then 0 else 1` advancing by `l1`; `Asm`/`LabAsm` advance by
their length unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def linesUpdLabLen {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) × Nat :=
  match lines with
  | [] => (acc.reverse, pos)
  | .label k1 k2 _l :: xs =>
      let l1 := if pos % 2 = 0 then 0 else 1
      linesUpdLabLen (pos + l1) xs (.label k1 k2 l1 :: acc)
  | .asm x1 x2 l :: xs =>
      linesUpdLabLen (pos + l) xs (.asm x1 x2 l :: acc)
  | .labAsm a w bytes l :: xs =>
      linesUpdLabLen (pos + l) xs (.labAsm a w bytes l :: acc)

/-- Exact HOL `lab_to_target$upd_lab_len_def`
(`lab_to_targetScript.sml:158-166`), clause for clause.  `[]` is `[]`; each
`Section s lines` is rewritten by `lines_upd_lab_len` seeded with `[]` from the
running position, and the remainder is rewritten from the resulting position. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def updLabLen {width : Nat} [NeZero width] (pos : Nat)
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  match sections with
  | [] => []
  | ⟨s, lines⟩ :: rest =>
      let (lines1, pos1) := linesUpdLabLen pos lines []
      let rest1 := updLabLen pos1 rest
      ⟨s, lines1⟩ :: rest1

end Flapjack.Compiler.Backend.LabToTarget
