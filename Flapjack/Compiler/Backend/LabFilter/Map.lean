import Flapjack.Compiler.Backend.LabFilter

namespace Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm

/-- Full original map characterization of skip filtering. The original full
HOL type is `alpha sec list`; its line/section syntax uses the native word
carrier, as confirmed together with both direct definitions. -/
@[hol "cakeml/compiler/backend/lab_filterScript.sml" "filter_skip_MAP"
  (words_as_type_indexed_bitvec)]
theorem filterSkipMap {width : Nat} [NeZero width]
    (program : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    filterSkip program = program.map (fun sect => ⟨sect.sectionId, sect.lines.filter notSkip⟩) := by
  induction program with
  | nil => rfl
  | cons sect rest ih => cases sect; simp only [filterSkip, List.map_cons, ih]

/-- Flapjack append consequence of the original map characterization, used in
Install code/oracle successor updates. No separate HOL declaration names it. -/
theorem filterSkipAppend {width : Nat} [NeZero width]
    (left right : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) :
    filterSkip (left ++ right) = filterSkip left ++ filterSkip right := by
  simp only [filterSkipMap, List.map_append]

end Flapjack.Compiler.Backend.LabFilter
