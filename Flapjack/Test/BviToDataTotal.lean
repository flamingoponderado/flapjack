module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileAgreement

@[expose] public section

/-! Original observations for total BVI-to-data lowering. -/
namespace Flapjack.Test.BviToDataTotal
open Flapjack.Compiler.Backend
open BviToData

example : compileSing 4 [] false [] (.var 5) = (.skip, 0, 4) := by
  simp [compileSing]

example : compileSing 4 [7] true [] (.var 0) = (.return [7], 4, 5) := by
  simp [compileSing]

example : compileSing 2 [] false [] (.letCall 1 0 3 [] (.return [.var 0])) =
    (.seq .skip (.call none (some 3) [] none), 2, 3) := by
  simp [compileSing, compileList, DataLang.mkTicks]

example (argc : Nat) (exp : Bvi.Exp) :
    compileExpBounded (Bvi.expBudget exp + 1) argc exp = some (BviToData.compileExp argc exp) := by
  exact compileExpBounded_agrees_all _ _ _

end Flapjack.Test.BviToDataTotal
