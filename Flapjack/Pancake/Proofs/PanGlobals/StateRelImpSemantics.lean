import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.Semantics.PanSem.TerminationWitness

namespace Flapjack.PanGlobalsStateRelImpSemantics
open Flapjack.Pancake.PanLang

/-- Canonical state roundtrips, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip, re-exported for this relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

open Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

/-- Original state_rel_imp_semantics: related initial states and source non-Fail
imply equality of the entire faithful HOL behaviour. compile_correct proves
pointwise result and FFI equality at every clock, so the failure predicates,
classical termination-choice predicates and complete divergence trace sets are
identical. There is no target-run or trace-prefix premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsHOL {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (start : MlS)
    (h : panGlobalsStateRelHOLExact true context source target ∧
      semantics source start ≠ HolBehaviour.fail) :
    semantics target start = semantics source start := by
  classical
  rcases h with ⟨hrel,hnonfail⟩
  have noError (clock : Nat) :
      (evaluateHOLFiniteState {source with clock := clock}
        (.call none start [])).1 ≠ some .error := by
    intro herror
    apply hnonfail
    unfold semantics
    dsimp only
    rw [if_pos]
    exact ⟨clock,by rw [herror]; trivial⟩
  have compiledEntry : compileProgExactHOL context (.call none start [] : ProgHOL width) =
      .call none start [] := by simp [compileProgExactHOL,compileExpExactHOLList]
  have observations (clock : Nat) :
      (evaluateHOLFiniteState {target with clock := clock} (.call none start [])).1 =
        (evaluateHOLFiniteState {source with clock := clock} (.call none start [])).1 ∧
      (evaluateHOLFiniteState {target with clock := clock} (.call none start [])).2.ffi =
        (evaluateHOLFiniteState {source with clock := clock} (.call none start [])).2.ffi := by
    have hclock : panGlobalsStateRelHOLExact true context
        {source with clock := clock} {target with clock := clock} :=
      ⟨hrel.1,hrel.2.1,hrel.2.2.1,hrel.2.2.2.1,hrel.2.2.2.2.1,
        rfl,hrel.2.2.2.2.2.2⟩
    rcases hs : evaluateHOLFiniteState {source with clock := clock} (.call none start []) with
      ⟨result,sourcePost⟩
    have hne : result ≠ some .error := by simpa only [hs,Prod.fst] using noError clock
    obtain ⟨targetPost,ht,hr⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
      (.call none start []) {source with clock := clock} result context
      {target with clock := clock} sourcePost ⟨hclock,hs,hne⟩
    rw [compiledEntry] at ht
    rcases hr with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hffi,_⟩
    rw [ht]
    exact ⟨rfl,hffi.symm⟩
  have results (clock : Nat) := (observations clock).1
  have events (clock : Nat) := congrArg (fun ffi : HolFfiState σ => ffi.ioEvents)
    (observations clock).2
  unfold semantics
  dsimp only
  simp only [terminationWitnessReduced,results,events]

end Flapjack.PanGlobalsStateRelImpSemantics
