import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Basis.Pure.MlString

/-!
# Faithful Cake label checking, padding and symbol collection (`lab_to_target`)

Exact definitions from `cakeml/compiler/backend/lab_to_targetScript.sml:168-245`.
`line_ok_light`/`sec_ok_light` are the light validity checks used by the
compiler before padding: only the labelled instructions that get re-encoded are
checked, `Call` is rejected and `Label`/`Asm` are accepted unconditionally.
`pad_bytes` extends a byte list to a requested length by repeating a `nop`
chunk; `add_nop`/`pad_section`/`pad_code` insert nop bytes into the lines of a
section up to a label boundary; `sec_length` sums the recorded line lengths of a
section and `get_symbols` threads that sum into a running position over the
section list.

HOL `line` and `sec` share a single type-indexed word parameter `'a`, so the
imported LabLang carriers are instantiated at HOL's actual carriers: `HolAsm`,
`HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm` and the opaque `MlString`, with
only HOL's `'a word` translated to the positive-width `BitVec width`.  HOL
`EVERY` is `List.all`, `REVERSE` is `List.reverse`, `LENGTH` is `.length`,
`TAKE`/`FLAT`/`REPLICATE` are `List.take`/`List.flatten`/`List.replicate`, and
`T`/`F` are `true`/`false`.  `line_ok_light`'s `asm_ok` calls read the exact
`asmOkExact` (`asm_ok_def`) over the exact `AsmConfigExact` carrier.

`pad_bytes` is polymorphic in HOL (`α list -> num -> α list -> α list`) and
carries no word carrier, so it is untagged-exact (`reviewed_exact`); every other
declaration here is stated over the linked `Line`/`Section` carriers and the
`AsmConfigExact` configuration, so it records the type-indexed word translation.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `lab_to_target$pad_bytes_def` (`lab_to_targetScript.sml:192-196`):
if `len` fits in `bytes`, return `bytes` unchanged; otherwise append
`FLAT (REPLICATE len nop)` and `TAKE len`.  HOL's `'a list` element type is
retained, so no word qualifier applies. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_bytes_def"]
def padBytes {α : Type} (bytes : List α) (len : Nat) (nop : List α) : List α :=
  let lenBytes := bytes.length
  if len ≤ lenBytes then bytes
  else (bytes ++ (List.replicate len nop).flatten).take len

/-- Exact HOL `lab_to_target$add_nop_def` (`lab_to_targetScript.sml:199-207`),
clause for clause.  `[]` is `[]`; a `Label` is kept and the rest is recursed; a
`Asm`/`LabAsm` appends `nop` to its bytes, increments its length by `1` and
keeps the remaining list `xs` unchanged (the clause does not recurse). -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "add_nop_def"
  (words_as_type_indexed_bitvec)]
def addNop {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :=
  match lines with
  | [] => []
  | .label l1 l2 len :: xs => .label l1 l2 len :: addNop nop xs
  | .asm x bytes len :: xs => .asm x (bytes ++ nop) (len + 1) :: xs
  | .labAsm y w bytes len :: xs => .labAsm y w (bytes ++ nop) (len + 1) :: xs

/-- Exact HOL `lab_to_target$pad_section_def`
(`lab_to_targetScript.sml:209-217`), clause for clause.  The empty list returns
`REVERSE aux`; a `Label l1 l2 len` pushes `Label l1 l2 0` and, when `len ≠ 0`,
prepends `add_nop nop aux`; `Asm`/`LabAsm` pad their bytes with `pad_bytes` and
push the line unchanged in length. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_section_def"
  (words_as_type_indexed_bitvec)]
def padSection {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :=
  match lines with
  | [] => aux.reverse
  | .label l1 l2 len :: xs =>
      padSection nop xs (.label l1 l2 0 ::
        (if len = 0 then aux else addNop nop aux))
  | .asm x bytes len :: xs =>
      padSection nop xs (.asm x (padBytes bytes len nop) len :: aux)
  | .labAsm y w bytes len :: xs =>
      padSection nop xs (.labAsm y w (padBytes bytes len nop) len :: aux)

/-- Exact HOL `lab_to_target$pad_code_def` (`lab_to_targetScript.sml:220-223`),
clause for clause.  `[]` is `[]`; `Section n xs :: ys` pads the section's lines
with `pad_section nop xs []` and recurses on the rest. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "pad_code_def"
  (words_as_type_indexed_bitvec)]
def padCode {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  match sections with
  | [] => []
  | ⟨n, xs⟩ :: ys => ⟨n, padSection nop xs []⟩ :: padCode nop ys

/-- Exact HOL `lab_to_target$sec_length_def`
(`lab_to_targetScript.sml:234-239`), clause for clause.  The accumulator `k`
starts the sum; `Label`/`Asm`/`LabAsm` all add their recorded length. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_length_def"
  (words_as_type_indexed_bitvec)]
def secLength {width : Nat} [NeZero width] :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Nat → Nat
  | [], k => k
  | .label _ _ l :: xs, k => secLength xs (k + l)
  | .asm _ _ l :: xs, k => secLength xs (k + l)
  | .labAsm _ _ _ l :: xs, k => secLength xs (k + l)

/-- Exact HOL `lab_to_target$get_symbols_def`
(`lab_to_targetScript.sml:241-245`), clause for clause.  Each section becomes
`(k, pos, len)` with `len = sec_length l 0`; the running position advances by
`len`. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "get_symbols_def"
  (words_as_type_indexed_bitvec)]
def getSymbols {width : Nat} [NeZero width] (pos : Nat)
    (sections : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    List (Nat × Nat × Nat) :=
  match sections with
  | [] => []
  | ⟨k, l⟩ :: secs =>
      let len := secLength l 0
      (k, pos, len) :: getSymbols (pos + len) secs

/-- Exact HOL `lab_to_target$line_ok_light_def`
(`lab_to_targetScript.sml:168-181`), clause for clause.  `Label` and `Asm` are
accepted; `Halt`/`Install`/`CallFFI` check `asm_ok (Jump w) c`; `Call` is
rejected (`F`); every other `LabAsm a w bytes l` checks `asm_ok (lab_inst w a)
c`.  The `asm_ok` calls read the exact `asmOkExact` over the exact
`AsmConfigExact` carrier. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "line_ok_light_def"
  (words_as_type_indexed_bitvec)]
def lineOkLight {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Bool
  | .label _ _ _ => true
  | .asm _ _ _ => true
  | .labAsm .halt w _ _ => asmOkExact (.jump w) config
  | .labAsm .install w _ _ => asmOkExact (.jump w) config
  | .labAsm (.callFFI _) w _ _ => asmOkExact (.jump w) config
  | .labAsm (.call _) _ _ _ => false
  | .labAsm a w _ _ => asmOkExact (labInst w a) config

/-- Exact HOL `lab_to_target$sec_ok_light_def`
(`lab_to_targetScript.sml:183-186`), clause for clause.  A `Section k ls` is ok
when `EVERY (line_ok_light c) ls` holds. -/
@[hol "cakeml/compiler/backend/lab_to_targetScript.sml" "sec_ok_light_def"
  (words_as_type_indexed_bitvec)]
def secOkLight {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Bool :=
  sec.lines.all (lineOkLight config)

end Flapjack.Compiler.Backend.LabToTarget
