module

public import Flapjack.Compiler.Backend.WordDepth

@[expose] public section

/-! The structural order on call trees used to bound stack depths. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Structural approximation of call trees: `leaf` is below everything,
everything is below `unknown`, and matching nodes compare componentwise. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "structure_le_def"]
def structureLe : WordDepth.CallTree → WordDepth.CallTree → Prop
  | .leaf, _ => True
  | _, .unknown => True
  | .const k1 t1, .const k2 t2 => k1 ≤ k2 ∧ structureLe t1 t2
  | .call n1 t2, .call m1 u2 => n1 = m1 ∧ structureLe t2 u2
  | .branch t1 t2, .branch u1 u2 => structureLe t1 u1 ∧ structureLe t2 u2
  | _, _ => False

end Flapjack.Compiler.Backend.DataToWord
