import Flapjack.Misc.ListEl
import Flapjack.RiscV.L3.Defs
import Flapjack.Pancake.WordConvs.NotCreated

/-! Flapjack regression checks for canonical arbitrary-value sharing. These
are supplemental kernel checks, not new HOL theorem ports or a chosen ARB value. -/
namespace Flapjack.Test.CanonicalL3ArbParity
open Flapjack.RiscV.L3

example {α : Type} [Inhabited α] :
    Flapjack.holArb α = Flapjack.holHdNil α := rfl

example (h : Nonempty WordMemOp) :
    holArbMemOp = @Flapjack.holArb WordMemOp h := rfl

example {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (p : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P p =
      notCreatedSubprogsWithMemOp (@Flapjack.holArb WordMemOp ⟨.store⟩) P p := by
  simpa only [holArbMemOp] using notCreatedSubprogsHOL_eq_withMemOp P p

example (e : ExceptionType) (badaddr : Option (BitVec 64)) (s : riscv_state) :
    NextFetch (setTrap (e, badaddr) s) =
      some (TransferControl.Trap { trap := e, badaddr := badaddr }) := by
  simp [setTrap, NextFetch, «write'NextFetch», holUpdate]

end Flapjack.Test.CanonicalL3ArbParity
