import Flapjack.Compiler.Backend.Bvl.GeneratedSize
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateClock

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack
open Flapjack.Compiler.Backend
open BvlSem

namespace EvalIndAltCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvalIndAltCarrier

/-- Alternative induction rule for the original clocked BVL evaluator. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "eval_ind_alt"
  (fmap_as_finite_support := [refs])]
theorem evalIndAlt {C F : Type}
    (P : List Bvl.Exp × List Value × Flapjack.Compiler.Backend.BvlSem.State C F → Prop)
    (steps :
      (∀ env s, P ([], env, s)) ∧
      (∀ x y xs env s,
        (∀ v3 s1 v1, evaluate [x] env s = (v3,s1) ∧ v3 = .val v1 → P (y::xs,env,s1)) ∧
        P ([x],env,s) → P (x::y::xs,env,s)) ∧
      (∀ n env s, P ([.var n],env,s)) ∧
      (∀ x1 x2 x3 env s,
        (∀ v2 s1 vs, evaluate [x1] env s = (v2,s1) ∧ v2 = .val vs ∧
          boolValue true ≠ @Flapjack.holHd Value ⟨unitValue⟩ vs ∧
          boolValue false = @Flapjack.holHd Value ⟨unitValue⟩ vs → P ([x3],env,s1)) ∧
        (∀ v2 s1 vs, evaluate [x1] env s = (v2,s1) ∧ v2 = .val vs ∧
          boolValue true = @Flapjack.holHd Value ⟨unitValue⟩ vs → P ([x2],env,s1)) ∧
        P ([x1],env,s) → P ([.ifThenElse x1 x2 x3],env,s)) ∧
      (∀ xs x2 env s,
        (∀ ys v2 s1 vs, Bvl.expListSizeHOL ys ≤ Bvl.expSizeHOL x2 ∧
          evaluate xs env s = (v2,s1) → P (ys,vs,s1)) ∧
        (∀ ys env, Bvl.expListSizeHOL ys ≤ Bvl.expSizeHOL x2 → P (ys,env,s)) ∧
        (∀ v2 s1 vs, evaluate xs env s = (v2,s1) ∧ v2 = .val vs → P ([x2],vs++env,s1)) ∧
        P (xs,env,s) → P ([.let xs x2],env,s)) ∧
      (∀ x env s, P ([x],env,s) → P ([.raise x],env,s)) ∧
      (∀ op xs env s, P (xs,env,s) → P ([.op op xs],env,s)) ∧
      (∀ x1 x2 env s1,
        (∀ v3 s v8 v, evaluate [x1] env s1 = (v3,s) ∧ v3 = .err v8 ∧
          v8 = .raise v → P ([x2],v::env,s)) ∧
        (∀ xs env, Bvl.expListSizeHOL xs ≤ Bvl.expSizeHOL x1 → P (xs,env,s1)) →
        P ([.handle x1 x2],env,s1)) ∧
      (∀ forceLoc n env s,
        (∀ thunkV mode v code args exp, n < env.length ∧
          thunkV = @Flapjack.holEl Value ⟨unitValue⟩ n env ∧
          destThunk thunkV s.refs = .isThunk mode v ∧ mode = .notEvaluated ∧
          s.clock ≠ 0 ∧ findCode (some forceLoc) [thunkV,v] s.code = some code ∧
          code = (args,exp) ∧ s.clock ≠ 0 → P ([exp],args,decClock 1 s)) →
        P ([.force forceLoc n],env,s)) ∧
      (∀ x env s, (s.clock ≠ 0 → P ([x],env,decClock 1 s)) → P ([.tick x],env,s)) ∧
      (∀ ticks dest xs env s1,
        (∀ v2 s vs code args exp, evaluate xs env s1 = (v2,s) ∧ v2 = .val vs ∧
          findCode dest vs s.code = some code ∧ code = (args,exp) ∧ ¬ s.clock < ticks + 1 →
          P ([exp],args,decClock (ticks+1) s)) ∧ P (xs,env,s1) →
        P ([.call ticks dest xs],env,s1))) :
    ∀ xs env s, P (xs,env,s) := by
  rcases steps with ⟨nilStep, consStep, varStep, ifStep, letStep, raiseStep, opStep,
    handleStep, forceStep, tickStep, callStep⟩
  intro xs env s
  apply clockWeightInduction (fun s : BvlSem.State C F => s.clock) Bvl.expListSizeHOL
    (motive := fun xs s => ∀ env, P (xs,env,s)) ?_ xs s env
  intro xs s ih smaller env
  cases xs with
  | nil => exact nilStep env s
  | cons x rest =>
    cases rest with
    | cons y ys =>
      apply consStep x y ys env s
      constructor
      · intro v3 s1 v1 ⟨run, eq⟩
        have bound := evaluate_clock_le [x] env s
        rw [run] at bound
        apply ih (y::ys) s1 bound
        simp only [Bvl.expListSizeHOL]
        omega
      · apply ih [x] s (by omega)
        simp only [Bvl.expListSizeHOL]
        have positive : 0 < Bvl.expSizeHOL y := by cases y <;> simp [Bvl.expSizeHOL] <;> omega
        omega
    | nil =>
      cases x with
      | var n => exact varStep n env s
      | raise body =>
        apply raiseStep body env s
        apply ih [body] s (by omega)
        simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
        omega
      | op op args =>
        apply opStep op args env s
        apply ih args s (by omega)
        simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
        omega
      | tick body =>
        apply tickStep body env s
        intro nonzero
        apply smaller [body] (decClock 1 s)
        simp [decClock]
        omega
      | force loc n =>
        apply forceStep loc n env s
        intro thunkV mode v code args exp ⟨_, _, _, _, nonzero, _, _, _⟩
        apply smaller [exp] (decClock 1 s)
        simp [decClock]
        omega
      | ifThenElse cond yes no =>
        apply ifStep cond yes no env s
        refine ⟨?_, ?_, ?_⟩
        · intro v2 s1 vs ⟨run, _, _, _⟩
          have bound := evaluate_clock_le [cond] env s
          rw [run] at bound
          apply ih [no] s1 bound
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · intro v2 s1 vs ⟨run, _, _⟩
          have bound := evaluate_clock_le [cond] env s
          rw [run] at bound
          apply ih [yes] s1 bound
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · apply ih [cond] s (by omega)
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
      | «let» bindings body =>
        apply letStep bindings body env s
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro ys v2 s1 vs ⟨size, run⟩
          have bound := evaluate_clock_le bindings env s
          rw [run] at bound
          apply ih ys s1 bound
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · intro ys env2 size
          apply ih ys s (by omega)
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · intro v2 s1 vs ⟨run, _⟩
          have bound := evaluate_clock_le bindings env s
          rw [run] at bound
          apply ih [body] s1 bound
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · apply ih bindings s (by omega)
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
      | handle body handler =>
        apply handleStep body handler env s
        constructor
        · intro v3 s1 v8 v ⟨run, _, _⟩
          have bound := evaluate_clock_le [body] env s
          rw [run] at bound
          apply ih [handler] s1 bound
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
        · intro xs env2 size
          apply ih xs s (by omega)
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
      | call ticks dest args =>
        apply callStep ticks dest args env s
        constructor
        · intro v2 s1 vs code values body ⟨run, _, _, _, enough⟩
          have bound := evaluate_clock_le args env s
          rw [run] at bound
          change s1.clock ≤ s.clock at bound
          apply smaller [body] (decClock (ticks + 1) s1)
          simp only [decClock]
          omega
        · apply ih args s (by omega)
          simp only [Bvl.expListSizeHOL, Bvl.expSizeHOL]
          omega
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
