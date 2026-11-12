module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Overapplication of generated generic closure calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace GenericFullCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end GenericFullCarrier

/-- An overapplied generic stub evaluates the saturated body and remaining call. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_generic_app_full"
  (fmap_as_finite_support := [refs])]
theorem evaluateGenericAppFull {C F α : Type} (n : Nat) (args : List BvlSem.Value)
    (st : Flapjack.Compiler.Backend.BvlSem.State C F) (remArgs : Nat)
    (vs : List BvlSem.Value) (l tag : Nat) (body : Bvl.Exp) (_clo : α) (maxApp : Nat)
    (premises : sptLookup l st.code = some (remArgs + 2, body) ∧
      n + 1 = args.length ∧ n > remArgs ∧ remArgs < maxApp) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block tag (.codePtr l :: .number (Int.ofNat remArgs) :: vs)]) st =
      if st.clock < remArgs + 1 then (.err (.abort .timeoutError), { st with clock := 0 })
      else
        match BvlSem.evaluate [body]
            (args.drop (args.length - (remArgs + 1)) ++
              [.block tag (.codePtr l :: .number (Int.ofNat remArgs) :: vs)])
            (BvlSem.decClock (remArgs + 1) st) with
        | (.val [v], st') =>
            match BvlSem.evaluate [mkClCall (.var 0) ((List.range (n - remArgs)).map (fun k => .var (k + 3)))]
                (v :: .number (Int.ofNat remArgs) :: .number (Int.ofNat remArgs - Int.ofNat args.length) ::
                  (args ++ [.block tag (.codePtr l :: .number (Int.ofNat remArgs) :: vs)])) st' with
            | (.val values, s2) => (.val [@Flapjack.holHd BvlSem.Value ⟨BvlSem.unitValue⟩ values], s2)
            | other => other
        | other => other := by
  rcases premises with ⟨lookup, length, over, bound⟩
  have step := evaluate_genericApp_over_step st maxApp n remArgs tag l args vs body length.symm (by omega) bound lookup
  have dropEq : args.length - (remArgs + 1) = n - remArgs := by omega
  rw [dropEq, ← length]
  rw [step]
  split
  · rfl
  · cases run : BvlSem.evaluate [body]
        (args.drop (n - remArgs) ++ [.block tag (.codePtr l :: .number (Int.ofNat remArgs) :: vs)])
        (BvlSem.decClock (remArgs + 1) st) with
    | mk result next =>
      cases result with
      | err e => simp
      | val values =>
        obtain ⟨v, rfl⟩ := BvlProps.evaluateSing body _ _ values next run
        simp only [List.singleton_append]
        cases run2 : BvlSem.evaluate [mkClCall (.var 0) ((List.range (n - remArgs)).map (fun k => .var (k + 3)))]
            (v :: .number (Int.ofNat remArgs) :: .number (Int.ofNat remArgs - Int.ofNat (n + 1)) ::
              (args ++ [.block tag (.codePtr l :: .number (Int.ofNat remArgs) :: vs)])) next with
        | mk result2 last =>
          cases result2 with
          | err e => simpa using run2
          | val values2 =>
            obtain ⟨w, rfl⟩ := BvlProps.evaluateSing _ _ _ values2 last run2
            simpa [Flapjack.holHd] using run2

end Flapjack.Compiler.Backend.ClosToBvl
