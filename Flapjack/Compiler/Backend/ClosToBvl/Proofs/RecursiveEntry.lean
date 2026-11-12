module

public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Shared-array selectors in recursive closure entries. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

namespace RecursiveEntryCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end RecursiveEntryCarrier

/-- Select a suffix of a shared recursive environment in order. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "genlist_el"
  (fmap_as_finite_support := [refs])]
theorem genlistEl {C F : Type} (skip : Nat)
    (st : Flapjack.Compiler.Backend.BvlSem.State C F) (r : Nat) (xs args : List BvlSem.Value)
    (p n : Nat) (env ys : List BvlSem.Value)
    (premises : st.refs.lookup r = some (.valueArray (ys ++ xs)) ∧ skip = ys.length) :
    BvlSem.evaluate ((List.range xs.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + skip))) [.var 0]))
      (.refPtr true r :: (args ++ .block 30 [.codePtr p, .number (Int.ofNat n), .refPtr true r] :: env)) st =
      (.val xs, st) := by
  rcases premises with ⟨stored, rfl⟩
  let context := args ++ .block 30 [.codePtr p, .number (Int.ofNat n), .refPtr true r] :: env
  have run : ∀ count, count ≤ xs.length →
      BvlSem.evaluate ((List.range count).map (fun i =>
        Bvl.Exp.op (.blockOp (.elemAt (i + ys.length))) [.var 0]))
        (.refPtr true r :: context) st = (.val (xs.take count), st) := by
    intro count bound
    induction count with
    | zero => simp [BvlSem.evaluate]
    | succ count ih =>
      have smaller : count ≤ xs.length := by omega
      have indexBound : count < xs.length := by omega
      rw [List.range_succ, List.map_append]
      change BvlSem.evaluateTuple (_, .refPtr true r :: context, st) = _
      rw [BvlProps.evaluateAppend]
      simp only [BvlSem.evaluateTuple, ih smaller, List.map_cons, List.map_nil]
      have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt (count + ys.length))) [.var 0]]
          (.refPtr true r :: context) st = (.val [xs[count]], st) := by
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, List.getElem?_cons_zero, stored,
          indexBound, Nat.add_comm]
      rw [elemRun]
      simp only [List.take_append_getElem indexBound]
  simpa [context] using run xs.length (by omega)

/-- A recursive entry binds its arguments and shared values before running its body. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_code_for_recc_case"
  (fmap_as_finite_support := [refs])]
theorem evaluateCodeForReccCase {C F : Type} (st : Flapjack.Compiler.Backend.BvlSem.State C F)
    (r : Nat) (xs args : List BvlSem.Value) (c : Bvl.Exp) (p n : Nat) (env : List BvlSem.Value)
    (stored : st.refs.lookup r = some (.valueArray xs)) :
    BvlSem.evaluate [(codeForReccCase xs.length args.length c).2]
      (args ++ .block 30 [.codePtr p, .number (Int.ofNat n), .refPtr true r] :: env) st =
    BvlSem.evaluate [c]
      (args ++ xs ++ [.refPtr true r] ++ args ++ .block 30 [.codePtr p, .number (Int.ofNat n), .refPtr true r] :: env) st := by
  let closure := BvlSem.Value.block 30 [.codePtr p, .number (Int.ofNat n), .refPtr true r]
  let context := args ++ closure :: env
  let bodyEnv := .refPtr true r :: context
  have refRun : BvlSem.evaluate [.op (.blockOp (.elemAt 2)) [.var args.length]] context st =
      (.val [.refPtr true r], st) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, closure, context]
  have argsRun : BvlSem.evaluate ((List.range args.length).map (fun i => Bvl.Exp.var (i + 1))) bodyEnv st =
      (.val args, st) := by
    have h := BvlProps.evaluateGenlistVars 1 bodyEnv args.length st (by simp [bodyEnv, context])
    simpa [BvlSem.evaluateTuple, bodyEnv, context] using h
  have envRun : BvlSem.evaluate ((List.range xs.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt i)) [.var 0])) bodyEnv st = (.val xs, st) := by
    simpa [bodyEnv, context, closure] using genlistEl 0 st r xs args p n env [] ⟨by simpa using stored, rfl⟩
  have bindings : BvlSem.evaluate (((List.range args.length).map (fun i => Bvl.Exp.var (i + 1))) ++
      ((List.range xs.length).map (fun i => Bvl.Exp.op (.blockOp (.elemAt i)) [.var 0]))) bodyEnv st =
      (.val (args ++ xs), st) := by
    change BvlSem.evaluateTuple (_, bodyEnv, st) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, envRun]
  change BvlSem.evaluate [.let [.op (.blockOp (.elemAt 2)) [.var args.length]]
    (.let (((List.range args.length).map (fun i => .var (i + 1))) ++
      ((List.range xs.length).map (fun i => .op (.blockOp (.elemAt i)) [.var 0]))) c)] context st = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, refRun]
  dsimp only
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.singleton_append]
  rw [bindings]
  simp [context, closure, List.append_assoc]

end Flapjack.Compiler.Backend.ClosToBvl
