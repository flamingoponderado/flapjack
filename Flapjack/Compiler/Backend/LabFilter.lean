import Flapjack.Compiler.Backend.LabLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef

/-!
# Faithful Cake `lab_filter` (`lab_filterScript.sml`)

Exact definitions from `cakeml/compiler/backend/lab_filterScript.sml:11-16`.
`not_skip` recognizes the single line `Asm (Asmi (Inst Skip)) _ _` and rejects
it; every other line is kept. `filter_skip` maps `FILTER not_skip` over the lines
of every section. Both operate on the width-indexed `labLang$line`/`sec`
carriers, so their tagged signatures instantiate `Line`/`Section` at the exact
HOL carriers (`HolAsm`, `HolMemop`, `HolAddr`, `HolCmp`, `HolRegImm`, `MlString`)
with HOL's `'a word` translated to the positive-width `BitVec width`
(`words_as_type_indexed_bitvec`).
-/

namespace Flapjack.Compiler.Backend.LabFilter

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `lab_filter$not_skip_def` (`lab_filterScript.sml:11`):
`not_skip l = case l of Asm (Asmi (Inst Skip)) _ _ => F | _ => T`. The skip
line is the only rejected constructor; the catch-all keeps `Label`, any other
`Asm` and every `LabAsm`. -/
@[hol "cakeml/compiler/backend/lab_filterScript.sml" "not_skip_def"
  (words_as_type_indexed_bitvec)]
def notSkip {width : Nat} [NeZero width] :
    Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width) → Bool
  | .asm (.asmi (.inst .skip)) _ _ => false
  | _ => true

/-- Exact HOL `lab_filter$filter_skip_def` (`lab_filterScript.sml:15-16`), both
clauses: `filter_skip [] = []` and
`filter_skip (Section n xs :: rest) = Section n (FILTER not_skip xs) ::
filter_skip rest`. -/
@[hol "cakeml/compiler/backend/lab_filterScript.sml" "filter_skip_def"
  (words_as_type_indexed_bitvec)]
def filterSkip {width : Nat} [NeZero width] :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) →
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
  | [] => []
  | ⟨n, xs⟩ :: rest => ⟨n, xs.filter notSkip⟩ :: filterSkip rest

end Flapjack.Compiler.Backend.LabFilter
