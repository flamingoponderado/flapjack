module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationDecode
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal
public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartEvaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Primitive-operation infrastructure for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
open ClosSem ClosProps

/-- The optimizer's state relation satisfies the general primitive-operation
state interface. This is Flapjack proof infrastructure. -/
theorem stateRelSimple {C F : Type} (c : Config) (g : Spt ValApprox) :
    simpleStateRel (ValueRel c g) (StateRel (C := C) (F := F) c g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr <;> simp_all [Flapjack.optionRel]
  · intro bytes t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some value =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup
      rfl
  · intro values t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some value =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup with
      | valueArray xs _ rel => exact ⟨xs, rfl, rel⟩
  · intro mode value t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some entry =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup with
      | thunk _ v _ rel => exact ⟨v, rfl, rel⟩
  · intro s t related
    exact ⟨related.2.2.2.2.2.1, related.2.2.2.2.2.2.2.2.1.1,
      related.2.2.2.2.2.2.2.1⟩
  · intro ffi s t related
    rcases related with ⟨aux, free, codeS, codeT, clock, _, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, rfl, maxApp, globals, refs, compiler, oracle⟩
  · intro bytes s t ptr related
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.byteArray bytes), compiler, oracle⟩
  · intro s t ptr xs ys ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.valueArray xs ys values), compiler, oracle⟩
  · intro s t ptr mode v w ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.thunk mode v w values), compiler, oracle⟩
  · intro s t xs ys ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, _, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, values, refs, compiler, oracle⟩

namespace PrimitiveSimulation

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Primitive operations preserve the known-function simulation relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doAppLemma {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (xs ys : List Value) (op : ClosLang.Op)
    (h : StateRel c g s t ∧ List.Forall₂ (ValueRel c g) xs ys) :
    match doApp op xs s with
    | .err err1 => ∃ err2, doApp op ys t = .err err2 ∧ Flapjack.SemanticPrimitivesProps.excRel (ValueRel c g) err1 err2
    | .val (x, s1) => ∃ y t1, ValueRel c g x y ∧ StateRel c g s1 t1 ∧ doApp op ys t = .val (y, t1) := by
  have result := ClosProps.PrimitiveTotal.simpleValRelDoApp (ValueRel c g) (StateRel c g) s t xs ys op
    ⟨valueRelSimple c g, stateRelSimple c g⟩ h
  cases run : doApp op xs s with
  | err error => simpa [run] using result
  | val pair => cases pair; simpa [run] using result

end PrimitiveSimulation

/-- Ordinary operation evaluation preserves related results and states after
related argument evaluations. This Flapjack helper isolates the dispatcher
step used by the optimizer's operation case. -/
theorem ordinaryOpSimulation {C F : Type} (c : Config) (g : Spt ValApprox)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args1 args2 : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 s1 : State (Spt ValApprox × C) F)
    (t0 t1 : State C F) (argRes1 argRes2 : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (sourceArgs : evaluate args1 env1 s0 = (argRes1, s1))
    (targetArgs : evaluate args2 env2 t0 = (argRes2, t1))
    (argsRel : Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel c g))
      (ValueRel c g) argRes1 argRes2) (state : StateRel c g s1 t1) :
    ∃ res1 res2 s2 t2,
      evaluate [.op trace op args1] env1 s0 = (res1, s2) ∧
      evaluate [.op trace op args2] env2 t0 = (res2, t2) ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel c g))
        (ValueRel c g) res1 res2 ∧ StateRel c g s2 t2 := by
  rw [evaluate_ordinaryOp_eq trace op args1 env1 s0 notInstall notForce, sourceArgs]
  rw [evaluate_ordinaryOp_eq trace op args2 env2 t0 notInstall notForce, targetArgs]
  cases argRes1 with
  | err err1 =>
    cases argRes2 with
    | val vals => simp [Flapjack.SemanticPrimitivesProps.resultRel] at argsRel
    | err err2 => exact ⟨.err err1, .err err2, s1, t1, rfl, rfl, argsRel, state⟩
  | val vals1 =>
    cases argRes2 with
    | err error => simp [Flapjack.SemanticPrimitivesProps.resultRel] at argsRel
    | val vals2 =>
      have values : List.Forall₂ (ValueRel c g) vals1.reverse vals2.reverse := List.rel_reverse argsRel
      have step := PrimitiveSimulation.doAppLemma c g s1 t1 vals1.reverse vals2.reverse op ⟨state, values⟩
      cases sourceApp : doApp op vals1.reverse s1 with
      | err error1 =>
        simp only [sourceApp] at step
        obtain ⟨error2, targetApp, errors⟩ := step
        dsimp only
        rw [sourceApp, targetApp]
        exact ⟨.err error1, .err error2, s1, t1, rfl, rfl, errors, state⟩
      | val pair =>
        obtain ⟨value1, s2⟩ := pair
        simp only [sourceApp] at step
        obtain ⟨value2, t2, valRel, states, targetApp⟩ := step
        dsimp only
        rw [sourceApp, targetApp]
        exact ⟨.val [value1], .val [value2], s2, t2, rfl, rfl, .cons valRel .nil, states⟩

/-- Ordinary operation simulation remains valid when the target operation is
rewritten by the smart-operation pass. This is Flapjack proof infrastructure
for the optimizer's operation case. -/
theorem ordinarySmartOpSimulation {C F : Type} (c : Config) (g : Spt ValApprox)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args1 args2 : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 s1 : State (Spt ValApprox × C) F)
    (t0 t1 : State C F) (argRes1 argRes2 : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (sourceArgs : evaluate args1 env1 s0 = (argRes1, s1))
    (targetArgs : evaluate args2 env2 t0 = (argRes2, t1))
    (argsRel : Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel c g))
      (ValueRel c g) argRes1 argRes2) (state : StateRel c g s1 t1)
    (res1 : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (s2 : State (Spt ValApprox × C) F)
    (sourceRun : evaluate [.op trace op args1] env1 s0 = (res1, s2))
    (noType : res1 ≠ .err (.abort .typeError)) :
    ∃ res2 t2, evaluate [ClosOp.smartOp trace op args2] env2 t0 = (res2, t2) ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel c g))
        (ValueRel c g) res1 res2 ∧ StateRel c g s2 t2 := by
  obtain ⟨r1, r2, last1, last2, run1, run2, related, states⟩ :=
    ordinaryOpSimulation c g trace op args1 args2 env1 env2 s0 s1 t0 t1 argRes1 argRes2
      notInstall notForce sourceArgs targetArgs argsRel state
  rw [sourceRun] at run1
  cases run1
  have targetNoType : r2 ≠ .err (.abort .typeError) := by
    intro eq
    subst r2
    cases res1 with
    | val values => simp [Flapjack.SemanticPrimitivesProps.resultRel] at related
    | err error =>
      cases error with
      | raise value => simp [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel] at related
      | abort abort =>
        simp [Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel] at related
        subst abort
        exact noType rfl
  exact ⟨r2, last2, ClosOp.smartOpThm trace op args2 env2 t0 last2 r2 ⟨run2, targetNoType⟩,
    related, states⟩

end Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
