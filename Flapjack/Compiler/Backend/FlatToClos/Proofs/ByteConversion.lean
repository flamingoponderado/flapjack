import Flapjack.Compiler.Backend.FlatToClos.Proofs.Identity

/-! Integer-to-byte conversion for the proof-side flat-to-closure relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The closure remainder by 256 is the integer encoding of the low byte,
including for negative integers. -/
theorem intToByte_remainder (value : Int) :
    (BitVec.ofInt 8 value).toNat = (value.fmod 256).toNat ∧
    (0 : Int) ≤ value.fmod 256 := by
  simp [BitVec.toNat_ofInt, Int.fmod_eq_emod, Int.emod_nonneg]

/-- The emitted modulo expression evaluates its argument and propagates any
argument error before applying the remainder operation. -/
theorem evaluate_mod256_argument {C F : Type} (state : ClosSem.State C F)
    (trace : BackendCommon.Tra) (expression : ClosLang.Exp) (env : List ClosSem.Value) :
    ClosSem.evaluate [.op trace (.intOp .mod)
      [.op trace (.intOp (.const 256)) [], expression]] env state =
      let run := ClosSem.evaluate [expression] env state
      match run with
      | (.err e, next) => (.err e, next)
      | (.val vs, next) =>
        match ClosSem.doApp (.intOp .mod) (vs.reverse ++ [.number 256]) next with
        | .err e => (.err e, next)
        | .val (v, last) => (.val [v], last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [ClosSem.evaluate, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]
  cases run : ClosSem.evaluate [expression] env state with
  | mk result next => (cases result <;> simp [ClosSem.fixClock, run]); rfl

end Flapjack.Compiler.Backend.FlatToClos
