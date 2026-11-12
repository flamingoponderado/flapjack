module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Unpacking closures and applying generated partial-application stubs. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The two HOL closure layouts and their accumulated argument counts. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "unpack_closure"]
inductive UnpackClosure : BvlSem.Value → (List BvlSem.Value × Nat × BvlSem.Value) → Prop where
  | closure (l : Nat) (total : Int) (fvs : List BvlSem.Value) (nonnegative : 0 ≤ total) :
      UnpackClosure (.block BackendCommon.closureTag (.codePtr l :: .number total :: fvs))
        ([], total.toNat, .block BackendCommon.closureTag (.codePtr l :: .number total :: fvs))
  | partialClosure (l : Nat) (remaining : Int) (clo : BvlSem.Value) (prev : List BvlSem.Value)
      (nonempty : prev ≠ []) (nonnegative : 0 ≤ remaining) :
      UnpackClosure (.block BackendCommon.partialAppTag (.codePtr l :: .number remaining :: clo :: prev))
        (prev, remaining.toNat + prev.length, clo)

namespace GenericPartialCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end GenericPartialCarrier

/-- A generic stub saves a still-unsaturated argument group. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_generic_app_partial"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenericAppPartial {C F : Type} (totalArgs : Nat) (prevArgs : List BvlSem.Value)
    (st : Flapjack.Compiler.Backend.BvlSem.State C F) (args : List BvlSem.Value)
    (cl subCl : BvlSem.Value) (maxApp : Nat)
    (premises : sptDomain st.code (partialAppFnLocation maxApp totalArgs (prevArgs.length + (args.length - 1))) ∧
      totalArgs < maxApp ∧ args.length < (totalArgs + 1) - prevArgs.length ∧ args.length ≠ 0 ∧
      ClosSem.getGlobal 0 st.globals = some (some (globalTable maxApp)) ∧
      UnpackClosure cl (prevArgs, totalArgs, subCl)) :
    BvlSem.evaluate [generateGenericApp maxApp (args.length - 1)] (args ++ [cl]) st =
      if st.clock < args.length - 1 then (.err (.abort .timeoutError), { st with clock := 0 })
      else (.val [.block BackendCommon.partialAppTag
        (.codePtr (partialAppFnLocation maxApp totalArgs (prevArgs.length + (args.length - 1))) ::
          .number (Int.ofNat (totalArgs - (prevArgs.length + args.length))) :: subCl :: args ++ prevArgs)],
        BvlSem.decClock (args.length - 1) st) := by
  rcases premises with ⟨domain, totalBound, remaining, nonempty, global, unpack⟩
  have len : args.length = (args.length - 1) + 1 := by omega
  cases unpack with
  | closure l total fvs nonnegative =>
    have toNat : Int.ofNat total.toNat = total := Int.toNat_of_nonneg nonnegative
    simp only [List.length_nil, Nat.sub_zero] at remaining
    have smaller : args.length - 1 < total.toNat := by omega
    have h := evaluate_genericApp_partial_new st maxApp (args.length - 1) total.toNat args fvs (.codePtr l)
      len smaller totalBound global
    simp only [← len] at h
    simpa only [toNat, BackendCommon.closureTag, BackendCommon.partialAppTag, List.length_nil,
      Nat.zero_add, List.append_nil] using h
  | partialClosure l remainingInt =>
    have nonnegative : 0 ≤ remainingInt := by assumption
    have toNat : Int.ofNat remainingInt.toNat = remainingInt := Int.toNat_of_nonneg nonnegative
    have smaller : args.length - 1 < remainingInt.toNat := by omega
    have h := evaluate_genericApp_partial_extend st maxApp (args.length - 1) remainingInt.toNat args prevArgs
      (.codePtr l) subCl len smaller totalBound global
    have subEq : remainingInt.toNat + prevArgs.length - (prevArgs.length + args.length) =
        remainingInt.toNat - args.length := by omega
    simp only [← len, toNat] at h
    simpa only [subEq, BackendCommon.partialAppTag, List.cons_append] using h

end Flapjack.Compiler.Backend.ClosToBvl
