module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

@[expose] public section

/-! Environment equivalence for closure calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace CallEnvironmentCarrier

/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

end CallEnvironmentCarrier

/-- Shifting the generated argument variables preserves the complete call. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "mk_call_simp2"
  (fmap_as_finite_support := [refs])]
theorem mkCallSimp2 {C F : Type} (n : Nat) (args stuff stuff' : List BvlSem.Value)
    (v : BvlSem.Value) (t : Flapjack.Compiler.Backend.BvlSem.State C F)
    (premises : n ≤ args.length ∧ stuff'.length ≠ 0) :
    BvlSem.evaluate [mkClCall (.var n) ((List.range n).map Bvl.Exp.var)]
      (args.take n ++ [v] ++ stuff) t =
    BvlSem.evaluate [mkClCall (.var 0) ((List.range n).map (fun k => .var (k + 1)))]
      (v :: (args ++ stuff')) t := by
  let env1 := args.take n ++ [v] ++ stuff
  let env2 := v :: (args ++ stuff')
  let xs := (List.range n).map Bvl.Exp.var
  let ys := (List.range n).map (fun k => Bvl.Exp.var (k + 1))
  have len : (args.take n).length = n := List.length_take_of_le premises.1
  have cl1 (u : BvlSem.State C F) : BvlSem.evaluate [.var n] env1 u = (.val [v], u) := by
    simp [BvlSem.evaluate, env1, len]
  have cl2 (u : BvlSem.State C F) : BvlSem.evaluate [.var 0] env2 u = (.val [v], u) := by
    simp [BvlSem.evaluate, env2]
  have run1 (u : BvlSem.State C F) : BvlSem.evaluate xs env1 u = (.val (args.take n), u) := by
    have h := BvlProps.evaluateGenlistVars 0 env1 n u (by simp [env1, len])
    simpa [BvlSem.evaluateTuple, xs, env1, len, List.take_append_of_le_length] using h
  have run2 (u : BvlSem.State C F) : BvlSem.evaluate ys env2 u = (.val (args.take n), u) := by
    have h := BvlProps.evaluateGenlistVars 1 env2 n u (by simp [env2]; omega)
    simpa [BvlSem.evaluateTuple, ys, env2, List.take_append_of_le_length premises.1] using h
  change BvlSem.evaluate [mkClCall (.var n) xs] env1 t =
    BvlSem.evaluate [mkClCall (.var 0) ys] env2 t
  apply evaluate_mkClCall_congr t env1 env2 (.var n) (.var 0) xs ys v (args.take n)
  · simp [xs, ys]
  · exact cl1
  · exact cl2
  · exact run1
  · exact run2

/-- Removing two leading environment values leaves the selected arguments unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "mk_cl_lem"
  (fmap_as_finite_support := [refs])]
theorem mkClLem {C F : Type} (l : Nat) (env : List BvlSem.Value) (a b c : BvlSem.Value)
    (st : Flapjack.Compiler.Backend.BvlSem.State C F) (bound : l < env.length) :
    BvlSem.evaluate ((List.range l).map (fun n => Bvl.Exp.var (n + 3))) (a :: b :: c :: env) st =
      BvlSem.evaluate ((List.range l).map (fun n => Bvl.Exp.var (n + 1))) (a :: env) st := by
  have h1 := BvlProps.evaluateGenlistVars 3 (a :: b :: c :: env) l st (by simp; omega)
  have h2 := BvlProps.evaluateGenlistVars 1 (a :: env) l st (by simp; omega)
  simpa [BvlSem.evaluateTuple] using h1.trans h2.symm

/-- The overapplication continuation ignores its two intermediate values. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_mk_cl_simpl"
  (fmap_as_finite_support := [refs])]
theorem evaluateMkClSimpl {C F : Type} (args : List BvlSem.Value) (n : Nat)
    (v a b : BvlSem.Value) (tag p : Nat) (xs : List BvlSem.Value)
    (st : Flapjack.Compiler.Backend.BvlSem.State C F) :
    BvlSem.evaluate [mkClCall (.var 0) ((List.range (args.length - (n + 1))).map (fun i => .var (i + 3)))]
      (v :: a :: b :: (args ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])) st =
    BvlSem.evaluate [mkClCall (.var 0) ((List.range (args.length - (n + 1))).map (fun i => .var (i + 1)))]
      (v :: (args ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)])) st := by
  let env := args ++ [.block tag (.codePtr p :: .number (Int.ofNat n) :: xs)]
  let count := args.length - (n + 1)
  have bound : count < env.length := by simp [count, env]; omega
  have run1 (u : BvlSem.State C F) :
      BvlSem.evaluate ((List.range count).map (fun i => .var (i + 3))) (v :: a :: b :: env) u =
        (.val (env.take count), u) := by
    simpa [BvlSem.evaluateTuple] using
      BvlProps.evaluateGenlistVars 3 (v :: a :: b :: env) count u (by simp; omega)
  have run2 (u : BvlSem.State C F) :
      BvlSem.evaluate ((List.range count).map (fun i => .var (i + 1))) (v :: env) u =
        (.val (env.take count), u) := (mkClLem count env v a b u bound).symm.trans (run1 u)
  change BvlSem.evaluate [mkClCall (.var 0) ((List.range count).map (fun i => .var (i + 3)))]
      (v :: a :: b :: env) st =
    BvlSem.evaluate [mkClCall (.var 0) ((List.range count).map (fun i => .var (i + 1)))] (v :: env) st
  apply evaluate_mkClCall_congr st _ _ _ _ _ _ v (env.take count)
  · simp
  · intro u; simp [BvlSem.evaluate]
  · intro u; simp [BvlSem.evaluate]
  · exact run1
  · exact run2

end Flapjack.Compiler.Backend.ClosToBvl
