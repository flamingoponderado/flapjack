import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation
import Flapjack.Compiler.Backend.Bvi.GeneratedSize

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
  have all : ∀ clock size xs (s : BviSem.BviState (Nat × C) F),
      s.clock = clock → Bvi.expListSizeHOL xs = size → P xs s := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock clockIH =>
      intro size
      induction size using Nat.strong_induction_on with
      | h size sizeIH =>
        intro xs s clockEq sizeEq
        apply step xs s
        intro ys t smaller
        rcases smaller with ⟨sizeLt, clockLe⟩ | clockLt
        · by_cases earlier : t.clock < clock
          · exact clockIH t.clock earlier _ ys t rfl rfl
          · have sameClock : t.clock = clock := by omega
            have lessSize : Bvi.expListSizeHOL ys < size := by omega
            exact sizeIH _ lessSize ys t sameClock rfl
        · have earlier : t.clock < clock := by omega
          exact clockIH t.clock earlier _ ys t rfl rfl
  intro xs s
  exact all s.clock (Bvi.expListSizeHOL xs) xs s rfl rfl

end Flapjack.Compiler.Backend.BviTailrec
