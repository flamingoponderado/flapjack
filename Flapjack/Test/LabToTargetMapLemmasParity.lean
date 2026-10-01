import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Test.LabToTargetSecondPassParity

/-!
# Native kernel replays of `lab_to_target_maplemmas_probe.out`

The expected observations come from the checked-in HOL probe
`scripts/hol-probes/lab_to_target_maplemmas_probeScript.sml`, which `EVAL`s the
two original `lab_to_target` MAP lemmas on concrete 64-bit
`labLang$sec` values (bead `flapjack-pxn.18.5.15.10.29`):

* `pad_code_MAP` (`lab_to_targetScript.sml:226`):
  `pad_code nop = MAP (λx. Section (Section_num x) (pad_section nop (Section_lines x) []))`.
* `prog_to_bytes_MAP` (`lab_to_targetScript.sml:341`):
  `∀ls. prog_to_bytes ls = FLAT (MAP (FLAT o MAP line_bytes o Section_lines) ls)`.

Each captured row evaluates both sides of the corresponding theorem.  The
`*Eq` rows replay the equality itself and the `*Lhs`/`*Rhs` rows replay the two
observed concrete results (`[Section 1 [Label 1 2 0; Asm (Asmi (Inst Skip))
[1w;2w;9w] 3]; Section 2 []]`, and `[1w;2w;3w]`).
-/

namespace Flapjack.Test.LabToTargetMapLemmasParity

open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack

private abbrev MlS := Flapjack.Basis.Pure.MlString.MlString
private abbrev Line64 :=
  Line (AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64))
    (AsmWithLab HolCmp (HolRegImm 64) MlS) (BitVec 64)
private abbrev Sec64 := Section Line64

private instance line64DecidableEq : DecidableEq Line64 := instDecidableEqLine
private instance sec64DecidableEq : DecidableEq Sec64 := instDecidableEqSection

private def w8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

private def padNop : List (BitVec 8) := [w8 9]

private def secList : List Sec64 :=
  [⟨1, [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 3]⟩, ⟨2, []⟩]

private def paddedSecList : List Sec64 :=
  [⟨1, [.label 1 2 0, .asm (.asmi (.inst .skip)) [w8 1, w8 2, w8 9] 3]⟩, ⟨2, []⟩]

private def padMapF (x : Sec64) : Sec64 :=
  ⟨x.sectionId, padSection padNop x.lines []⟩

-- PadCodeMapEmptyEq
example :
    padCode padNop ([] : List Sec64) = ([] : List Sec64).map padMapF := by
  decide +kernel

-- PadCodeMapConcreteEq
example : padCode padNop secList = secList.map padMapF := by
  decide +kernel

-- PadCodeMapConcreteLhs
example : padCode padNop secList = paddedSecList := by
  decide +kernel

-- PadCodeMapConcreteRhs
example : secList.map padMapF = paddedSecList := by
  decide +kernel

private def bytesCode : List Sec64 :=
  [⟨1, [.label 1 2 3, .asm (.asmi (.inst .skip)) [w8 1, w8 2] 2]⟩,
   ⟨2, []⟩,
   ⟨3, [.labAsm (.jump (.lab 1 0)) (0 : BitVec 64) [w8 3] 1]⟩]

private def bytesMapF (s : Sec64) : List (BitVec 8) :=
  (s.lines.map lineBytes).flatten

-- ProgToBytesMapEmptyEq
example :
    progToBytes ([] : List Sec64) = ([].map bytesMapF).flatten := by
  simp only [progToBytes.eq_1, List.map_nil, List.flatten_nil]

-- ProgToBytesMapConcreteEq
example : progToBytes bytesCode = (bytesCode.map bytesMapF).flatten := by
  simp only [progToBytes.eq_1, progToBytes.eq_2, progToBytes.eq_3, bytesCode,
    bytesMapF, lineBytes, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.nil_append, w8]
  decide +kernel

-- ProgToBytesMapConcreteLhs
example : progToBytes bytesCode = [w8 1, w8 2, w8 3] := by
  simp only [progToBytes.eq_1, progToBytes.eq_2, progToBytes.eq_3, bytesCode,
    lineBytes, w8]
  decide +kernel

-- ProgToBytesMapConcreteRhs
example : (bytesCode.map bytesMapF).flatten = [w8 1, w8 2, w8 3] := by
  simp only [bytesCode, bytesMapF, lineBytes, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.nil_append, w8]
  decide +kernel

def runChecks : IO Bool := do
  IO.println "PASS lab_to_target pad_code_MAP/prog_to_bytes_MAP match all 8 oracle rows"
  pure true

end Flapjack.Test.LabToTargetMapLemmasParity
