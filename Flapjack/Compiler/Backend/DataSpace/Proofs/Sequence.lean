import Flapjack.Compiler.Backend.DataSpace.Proofs.Simulation

/-! Composition of reservation simulations through sequences. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- When the second component leaves no deferred reservation, the pass
retains a sequence except for its skip and reservation special cases. -/
theorem compile_seq_plain_of_noReservation (first second body : DataLang.Prog)
    (found : space second = .inl body) (notSkip : first ≠ .skip)
    (notSpace : ∀ amount names, first ≠ .makeSpace amount names) :
    compile (.seq first second) = .seq (compile first) (compile second) := by
  cases first <;> simp_all [compile, space, pMakeSpace]

/-- A deferred reservation also stays in the second component when the
first instruction is not one of the hoistable forms. -/
theorem compile_seq_plain_of_nonHoistable (first second : DataLang.Prog) (amount : Nat)
    (names : NumSet) (body : DataLang.Prog) (found : space second = .inr (amount, names, body))
    (notSkip : first ≠ .skip) (notSpace : ∀ amount names, first ≠ .makeSpace amount names)
    (notMove : ∀ dest src, first ≠ .move dest src)
    (notAssign : ∀ dest op args, first ≠ .assign dest op args none) :
    compile (.seq first second) = .seq (compile first) (compile second) := by
  cases first <;> simp_all [compile, space, pMakeSpace]

end Flapjack.Compiler.Backend.DataSpace
