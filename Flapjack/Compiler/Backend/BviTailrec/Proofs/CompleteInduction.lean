import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation
import Flapjack.Compiler.Backend.Bvi.GeneratedSize
import Flapjack.Misc.ClockWeightInduction

namespace Flapjack.Compiler.Backend.BviTailrec

namespace CompleteInductionCarrier
/-- The BVI reference-map carrier roundtrips through its finite-support view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end CompleteInductionCarrier

/-- Complete induction on the state clock and HOL's generated expression-list size. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "evaluate_complete_ind"
  (fmap_as_finite_support := [refs])]
theorem evaluate_complete_ind {C F : Type}
    (P : List Bvi.Exp → BviSem.BviState (Nat × C) F → Prop)
    (step : ∀ xs s, (∀ ys t,
      (Bvi.expListSizeHOL ys < Bvi.expListSizeHOL xs ∧ t.clock ≤ s.clock) ∨
        t.clock < s.clock → P ys t) → P xs s) :
    ∀ xs s, P xs s := by
  apply clockWeightInduction (α := List Bvi.Exp) (σ := BviSem.BviState (Nat × C) F)
    (·.clock) Bvi.expListSizeHOL (motive := P)
  intro xs s sizeIH clockIH
  apply step xs s
  intro ys t smaller
  rcases smaller with ⟨sizeLt, clockLe⟩ | clockLt
  · exact sizeIH ys t clockLe sizeLt
  · exact clockIH ys t clockLt

end Flapjack.Compiler.Backend.BviTailrec
