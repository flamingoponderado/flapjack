import Flapjack.Compiler.Backend.LabProps.Labels
import Flapjack.Compiler.Backend.LabProps.LabelSets

/-!
# labProps `EVERY_sec_label_ok`

`EVERY_sec_label_ok` (`cakeml/compiler/backend/semantics/labPropsScript.sml:1279-1286`): a line
list's extracted labels all belong to section `n` and are nonzero exactly when every line is
`sec_label_ok n`. HOL's `EVERY` is `∀ x ∈ l`; the Boolean `⇔` is `↔`.
-/

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- HOL `EVERY_sec_label_ok` (`labPropsScript.sml:1279-1286`); HOL's free `n l` are explicit. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "EVERY_sec_label_ok"
  (words_as_type_indexed_bitvec)]
theorem EVERY_sec_label_ok {width : Nat} [NeZero width] (n : Nat)
    (l : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    (∀ x ∈ LabelSets.extractLabels l, x.1 = n ∧ x.2 ≠ 0) ↔ ∀ line ∈ l, secLabelOk n line := by
  induction l with
  | nil => simp [LabelSets.extractLabels]
  | cons line rest ih =>
    cases line <;> simp_all [LabelSets.extractLabels, secLabelOk]

end Flapjack.Compiler.Backend.LabProps
