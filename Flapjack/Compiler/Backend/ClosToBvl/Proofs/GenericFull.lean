module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CallEnvironment

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

/-- A closure call either enters its body directly or runs the overapplication stub. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_mk_cl_call"
  (fmap_as_finite_support := [refs])]
theorem evaluateMkClCall {C F α : Type} (cl : Bvl.Exp) (env : List BvlSem.Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) (tag p n : Nat)
    (args : List Bvl.Exp) (values : List BvlSem.Value) (body : Bvl.Exp) (_exp2 : α)
    (xs : List BvlSem.Value) (maxApp : Nat)
    (premises : BvlSem.evaluate [cl] env s = (.val [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)], s) ∧
      BvlSem.evaluate args env s = (.val values, s) ∧
      sptLookup p s.code = some (n + 2, body) ∧
      sptLookup (genericAppFnLocation (values.length - 1)) s.code =
        some (values.length + 1, generateGenericApp maxApp (values.length - 1)) ∧
      n ≤ values.length - 1 ∧ n < maxApp ∧ args.length ≠ 0) :
    BvlSem.evaluate [mkClCall cl args] env s =
      if n = args.length - 1 then
        if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [body]
          (values ++ [.block tag (.codePtr p :: .number (Int.ofNat (args.length - 1)) :: xs)])
          (BvlSem.decClock args.length s)
      else
        if s.clock < n + 2 then (.err (.abort .timeoutError), { s with clock := 0 })
        else
          match BvlSem.evaluate [body]
              (values.drop (values.length - (n + 1)) ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])
              (BvlSem.decClock (n + 2) s) with
          | (.val [v], st') =>
              match BvlSem.evaluate [mkClCall (.var 0) ((List.range (values.length - (n + 1))).map (fun k => .var (k + 1)))]
                  (v :: (values ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])) st' with
              | (.val vs, s2) => (.val [@Flapjack.holHd BvlSem.Value ⟨BvlSem.unitValue⟩ vs], s2)
              | other => other
          | other => other := by
  rcases premises with ⟨clRun, argsRun, lookup, genericLookup, enoughArgs, nBound, nonzero⟩
  have length : args.length = values.length := BvlProps.evaluateImpLength args env s values s argsRun
  have nonempty : args ≠ [] := by intro h; simp [h] at nonzero
  by_cases equal : n = args.length - 1
  · simp only [equal, ↓reduceIte]
    subst n
    apply evaluate_mkClCall_direct s env cl args values tag p xs body clRun argsRun nonempty
    have count : args.length - 1 + 2 = values.length + 1 := by omega
    simpa [count] using lookup
  · simp only [equal, ↓reduceIte]
    have different : args.length - 1 ≠ n := Ne.symm equal
    have callRun := evaluate_mkClCall_generic s env cl args values tag n (.codePtr p) xs
      (generateGenericApp maxApp (values.length - 1)) clRun argsRun different (by simpa [length] using genericLookup)
    rw [callRun]
    by_cases zero : s.clock = 0
    · simp [zero]
    · simp only [zero, ↓reduceIte]
      have count : (values.length - 1) + 1 = values.length := by omega
      have over : values.length - 1 > n := by omega
      have lookupDec : sptLookup p (BvlSem.decClock 1 s).code = some (n + 2, body) := by
        simpa [BvlSem.decClock] using lookup
      have run := evaluateGenericAppFull (values.length - 1) values (BvlSem.decClock 1 s) n xs p tag body () maxApp
        ⟨lookupDec, count, over, nBound⟩
      rw [run]
      have clockTest : (BvlSem.decClock 1 s).clock < n + 1 ↔ s.clock < n + 2 := by
        simp only [BvlSem.decClock]
        omega
      simp only [clockTest]
      split
      · simp [BvlSem.decClock]
      · have decEq : BvlSem.decClock (n + 1) (BvlSem.decClock 1 s) = BvlSem.decClock (n + 2) s := by
          simp only [BvlSem.decClock]
          congr 1
          omega
        rw [decEq]
        have subEq : values.length - 1 - n = values.length - (n + 1) := by omega
        rw [subEq]
        cases bodyRun : BvlSem.evaluate [body]
            (values.drop (values.length - (n + 1)) ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])
            (BvlSem.decClock (n + 2) s) with
        | mk result next =>
          cases result with
          | err e => rfl
          | val vals =>
            cases vals with
            | nil => rfl
            | cons v tail =>
              cases tail with
              | cons w rest => rfl
              | nil =>
                have envEq := evaluateMkClSimpl values n v (.number (Int.ofNat n))
                  (.number (Int.ofNat n - Int.ofNat values.length)) tag p xs next
                dsimp only
                rw [envEq]

/-- A generated closure call executes the exact or overapplied branch. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_mk_cl_call_spec"
  (fmap_as_finite_support := [refs])]
theorem evaluateMkClCallSpec {C F : Type}
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) (env : List BvlSem.Value)
    (tag p n : Nat) (args : List BvlSem.Value) (body : Bvl.Exp) (xs : List BvlSem.Value) (maxApp : Nat)
    (premises : sptLookup p s.code = some (n + 2, body) ∧
      sptLookup (genericAppFnLocation (args.length - 1)) s.code =
        some (args.length + 1, generateGenericApp maxApp (args.length - 1)) ∧
      n ≤ args.length - 1 ∧ n < maxApp ∧ args.length ≠ 0) :
    BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
      (args ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)] ++ env) s =
      if n = args.length - 1 then
        if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [body]
          (args ++ [.block tag (.codePtr p :: .number (Int.ofNat (args.length - 1)) :: xs)])
          (BvlSem.decClock args.length s)
      else
        if s.clock < n + 2 then (.err (.abort .timeoutError), { s with clock := 0 })
        else
          match BvlSem.evaluate [body]
              (args.drop (args.length - (n + 1)) ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])
              (BvlSem.decClock (n + 2) s) with
          | (.val [v], st') =>
              match BvlSem.evaluate [mkClCall (.var 0) ((List.range (args.length - (n + 1))).map (fun k => .var (k + 1)))]
                  (v :: (args ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])) st' with
              | (.val vs, s2) => (.val [@Flapjack.holHd BvlSem.Value ⟨BvlSem.unitValue⟩ vs], s2)
              | other => other
          | other => other := by
  let closure := BvlSem.Value.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)
  let context := args ++ [closure] ++ env
  have clRun : BvlSem.evaluate [.var args.length] context s = (.val [closure], s) := by
    simp [BvlSem.evaluate, context]
  have argsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var) context s = (.val args, s) := by
    have bound : args.length ≤ context.length := by simp [context]
    simpa [BvlSem.evaluateTuple, context] using BvlProps.evaluateGenlistVars 0 context args.length s bound
  have run := evaluateMkClCall (.var args.length) context s tag p n ((List.range args.length).map Bvl.Exp.var)
    args body () xs maxApp ⟨by simpa [closure] using clRun, argsRun, premises.1, premises.2.1,
      premises.2.2.1, premises.2.2.2.1, by simpa using premises.2.2.2.2⟩
  simpa [context, closure] using run

end Flapjack.Compiler.Backend.ClosToBvl
