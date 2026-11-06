import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.ClosSem.Int

/-! Agreement of the closure and BVL integer primitives. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Flapjack helper for the numeric and Boolean values returned by integer
operations; no other closure value can be returned by these primitives. -/
def intResultToBvl : ClosSem.Value → Option BvlSem.Value
  | .number n => some (.number n)
  | .block tag [] => some (.block tag [])
  | _ => none

/-- Flapjack simulation of integer operations on numeric arguments. The full
pass relation, including nonnumeric arguments, is not established here. -/
theorem doIntApp_numbers (op : ClosLang.IntOp) (args : List Int) :
    BvlSem.doIntApp op (args.map BvlSem.Value.number) =
      (ClosSem.doIntApp op (args.map ClosSem.Value.number)).bind intResultToBvl := by
  cases op <;> cases args with
  | nil => simp [BvlSem.doIntApp, ClosSem.doIntApp, intResultToBvl]
  | cons a args =>
    cases args with
    | nil => simp [BvlSem.doIntApp, ClosSem.doIntApp,
        BvlSem.boolValue, ClosSem.boolValue, BackendCommon.boolToTag] <;>
        split <;> simp [intResultToBvl]
    | cons b args =>
      cases args <;> simp [BvlSem.doIntApp, ClosSem.doIntApp, intResultToBvl,
        BvlSem.boolValue, ClosSem.boolValue, BackendCommon.boolToTag] <;>
        split <;> simp [intResultToBvl]

end Flapjack.Compiler.Backend.ClosToBvl
