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

/-- Generic application creates a partial closure from an ordinary closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_generic_app1"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenericApp1 {C F : Type} (maxApp : Nat) :
    ∀ (n : Nat) (args : List BvlSem.Value) (st : Flapjack.Compiler.Backend.BvlSem.State C F)
      (total : Nat) (l : Nat) (fvs : List BvlSem.Value) (cl : BvlSem.Value),
      sptDomain st.code (partialAppFnLocation maxApp total n) ∧
      n < total ∧ total < maxApp ∧ n + 1 = args.length ∧
      ClosSem.getGlobal 0 st.globals = some (some (globalTable maxApp)) ∧
      cl = .block BackendCommon.closureTag (.codePtr l :: .number (Int.ofNat total) :: fvs) →
      BvlSem.evaluate [generateGenericApp maxApp n] (args ++ [cl]) st =
        if st.clock < n then (.err (.abort .timeoutError), { st with clock := 0 })
        else (.val [.block BackendCommon.partialAppTag
          (.codePtr (partialAppFnLocation maxApp total n) ::
            .number (Int.ofNat (total - (n + 1))) :: cl :: args)], BvlSem.decClock n st) := by
  intro n args st total l fvs cl ⟨_, bound, totalBound, length, global, clEq⟩
  subst cl
  have h := evaluate_genericApp_partial_new st maxApp n total args fvs (.codePtr l)
    length.symm bound totalBound global
  simpa only [BackendCommon.closureTag, BackendCommon.partialAppTag] using h

/-- Generic application extends an existing partial closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_generic_app2"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenericApp2 {C F : Type} (maxApp : Nat) :
    ∀ (n : Nat) (args : List BvlSem.Value) (st : Flapjack.Compiler.Backend.BvlSem.State C F)
      (remaining : Nat) (prev : List BvlSem.Value) (l : Nat) (clo cl : BvlSem.Value),
      sptDomain st.code (partialAppFnLocation maxApp (remaining + prev.length) (n + prev.length)) ∧
      n < remaining ∧ n + 1 = args.length ∧ prev.length > 0 ∧
      remaining + prev.length < maxApp ∧
      ClosSem.getGlobal 0 st.globals = some (some (globalTable maxApp)) ∧
      cl = .block BackendCommon.partialAppTag (.codePtr l :: .number (Int.ofNat remaining) :: clo :: prev) →
      BvlSem.evaluate [generateGenericApp maxApp n] (args ++ [cl]) st =
        if st.clock < n then (.err (.abort .timeoutError), { st with clock := 0 })
        else (.val [.block BackendCommon.partialAppTag
          (.codePtr (partialAppFnLocation maxApp (remaining + prev.length) (n + prev.length)) ::
            .number (Int.ofNat remaining - Int.ofNat (n + 1)) :: clo :: args ++ prev)],
          BvlSem.decClock n st) := by
  intro n args st remaining prev l clo cl ⟨_, bound, length, _, totalBound, global, clEq⟩
  subst cl
  have h := evaluate_genericApp_partial_extend st maxApp n remaining args prev (.codePtr l) clo
    length.symm bound totalBound global
  have sub : Int.ofNat remaining - Int.ofNat (n + 1) = Int.ofNat (remaining - (n + 1)) := by
    exact (Int.ofNat_sub (by omega)).symm
  simpa only [BackendCommon.partialAppTag, Nat.add_comm n prev.length, sub, List.cons_append] using h

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
