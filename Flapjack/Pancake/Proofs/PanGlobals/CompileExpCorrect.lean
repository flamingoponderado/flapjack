import Flapjack.Pancake.Proofs.PanGlobals.CompileExpLeaves
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpRStruct
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpRField
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpNamed
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpOperators
import Flapjack.Pancake.Proofs.PanGlobals.CompileExpCmpShift

namespace Flapjack.PanGlobalsCompileExpCorrect
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

/-- Full HOL103-157 expression theorem. Structural induction discharges every
recursive constructor premise internally, including the original well-formed-shape
guard for Load. No induction hypothesis or target evaluation is a public premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectHOL {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (expression : ExpHOL width)
    (value : ValueHOL width) (context : PanGlobalsContextExact width)
    (target : PanSemStateFiniteExact width σ) :
    (panGlobalsStateRelHOLExact true context source target ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value) →
    @PanSemStateFiniteExact.evalHOLFinite width σ _ target
      (fun a => Classical.propDecidable (target.memaddrs a))
      (compileExpExactHOL context expression) = some value := by
  classical
  let P := fun e : ExpHOL width => ∀ (v : ValueHOL width)
    (ctxt : PanGlobalsContextExact width) (tgt : PanSemStateFiniteExact width σ),
    (panGlobalsStateRelHOLExact true ctxt source tgt ∧
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) e = some v) →
    @PanSemStateFiniteExact.evalHOLFinite width σ _ tgt
      (fun a => Classical.propDecidable (tgt.memaddrs a))
      (compileExpExactHOL ctxt e) = some v
  have all : ∀ e, P e := by
    intro e
    apply ExpHOL.rec (motive_1 := P)
      (motive_2 := fun es => ∀ e ∈ es, P e)
      (motive_3 := fun _ => True) (motive_4 := fun _ => True)
    · intro c v ctxt tgt
      exact PanGlobalsCompileExpLeaves.compileExpCorrectConstHOL source tgt ctxt c v
    · intro kind n v ctxt tgt
      cases kind with
      | «local» => exact PanGlobalsCompileExpLeaves.compileExpCorrectLocalHOL source tgt ctxt n v
      | global => exact panGlobalsCompileExpCorrectGlobalVarCaseExact source n v ctxt tgt
    · intro es ih v ctxt tgt
      exact PanGlobalsCompileExpRStruct.compileExpCorrectRStructHOL source tgt ctxt es v
        (fun e he result => ih e he result ctxt tgt)
    · intro i arg ih v ctxt tgt
      exact PanGlobalsCompileExpRField.compileExpCorrectRFieldHOL source tgt ctxt i arg v
        (fun result => ih result ctxt tgt)
    · intro n fields _ v ctxt tgt
      exact PanGlobalsCompileExpNamed.compileExpCorrectNStructHOL source tgt ctxt n fields v
    · intro n arg _ v ctxt tgt
      exact PanGlobalsCompileExpNamed.compileExpCorrectNFieldHOL source tgt ctxt n arg v
    · intro sh addr ih v ctxt tgt
      exact panGlobalsCompileExpCorrectLoadCaseExact source tgt ctxt sh addr v (fun _ => ih)
    · intro addr ih v ctxt tgt
      exact panGlobalsCompileExpCorrectLoad32CaseExact source tgt ctxt addr v ih
    · intro addr ih v ctxt tgt
      exact panGlobalsCompileExpCorrectLoadByteCaseExact source tgt ctxt addr v ih
    · intro op es ih v ctxt tgt
      exact PanGlobalsCompileExpOperators.compileExpCorrectOpHOL source tgt ctxt op es v
        (fun e he result => ih e he result ctxt tgt)
    · intro op es ih v ctxt tgt
      exact PanGlobalsCompileExpOperators.compileExpCorrectPanopHOL source tgt ctxt op es v
        (fun e he result => ih e he result ctxt tgt)
    · intro op left right ihl ihr v ctxt tgt
      exact PanGlobalsCompileExpCmpShift.compileExpCorrectCmpHOL source tgt ctxt op left right v
        (fun result => ihl result ctxt tgt) (fun result => ihr result ctxt tgt)
    · intro op left right ihl ihr v ctxt tgt
      exact PanGlobalsCompileExpCmpShift.compileExpCorrectShiftHOL source tgt ctxt op left right v
        (fun result => ihl result ctxt tgt) (fun result => ihr result ctxt tgt)
    · intro v ctxt tgt
      exact PanGlobalsCompileExpLeaves.compileExpCorrectBaseAddrHOL source tgt ctxt v
    · intro v ctxt tgt
      exact PanGlobalsCompileExpLeaves.compileExpCorrectTopAddrHOL source tgt ctxt v
    · intro v ctxt tgt
      exact PanGlobalsCompileExpLeaves.compileExpCorrectBytesInWordHOL source tgt ctxt v
    · intro e he
      exact False.elim (List.not_mem_nil he)
    · intro head tail ihh iht e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ihh
      · exact iht e he
    · trivial
    · intros; trivial
    · intros; trivial
  exact all expression value context target

end Flapjack.PanGlobalsCompileExpCorrect
