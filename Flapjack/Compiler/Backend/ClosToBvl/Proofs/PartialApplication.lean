module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Semantics of generated partial-application completion stubs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace PartialApplicationCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end PartialApplicationCarrier

/-- A completion stub restores all argument groups and calls the stored body. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_partial_app_fn"
  (fmap_as_finite_support := [refs])]
theorem evaluatePartialAppFn {C F : Type} (numArgs : Nat) (args : List BvlSem.Value)
    (numArgs' : BvlSem.Value) (prevArgs : List BvlSem.Value) (tag : Nat) (num : BvlSem.Value)
    (tag' l : Nat) (l' : BvlSem.Value) (fvs : List BvlSem.Value) (body : Bvl.Exp)
    (code : Spt (Nat × Bvl.Exp))
    (premises : sptLookup l code = some (args.length + prevArgs.length + 1, body) ∧
      prevArgs.length ≠ 0 ∧ prevArgs.length < numArgs ∧ numArgs = prevArgs.length + args.length) :
    ∀ st : Flapjack.Compiler.Backend.BvlSem.State C F,
      BvlSem.evaluate [generatePartialAppClosureFn (numArgs - 1) (prevArgs.length - 1)]
        (args.drop (args.length + prevArgs.length - numArgs) ++
          [.block tag (l' :: num :: .block tag' (.codePtr l :: numArgs' :: fvs) :: prevArgs)])
        { st with code := code } =
      if st.clock = 0 then (.err (.abort .timeoutError), { st with code := code })
      else BvlSem.evaluate [body]
        (args.drop (args.length + prevArgs.length - numArgs) ++ prevArgs ++
          [.block tag' (.codePtr l :: numArgs' :: fvs)])
        (BvlSem.decClock 1 { st with code := code }) := by
  intro st
  rcases premises with ⟨lookup, nonzero, bound, total⟩
  have savedPos : 0 < prevArgs.length := by omega
  have dropZero : args.length + prevArgs.length - numArgs = 0 := by omega
  have newCount : (numArgs - 1) - (prevArgs.length - 1) = args.length := by omega
  have savedCount : prevArgs.length - 1 + 1 = prevArgs.length := by omega
  have run := evaluate_partialAppClosureFn { st with code := code } (numArgs - 1) (prevArgs.length - 1)
    args prevArgs l' l tag tag' num (numArgs' :: fvs) body newCount savedCount (by simpa using lookup)
  by_cases zero : st.clock = 0
  · simpa [dropZero, zero] using run
  · simpa [dropZero, zero] using run

end Flapjack.Compiler.Backend.ClosToBvl
