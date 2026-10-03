import Flapjack.Pancake.Proofs.PanStructs.CompileExpAtomic
import Flapjack.Pancake.Proofs.PanStructs.CompileExpVar
import Flapjack.Pancake.Proofs.PanStructs.CompileExpRStruct
import Flapjack.Pancake.Proofs.PanStructs.CompileExpRField
import Flapjack.Pancake.Proofs.PanStructs.CompileExpNStruct
import Flapjack.Pancake.Proofs.PanStructs.CompileExpNField
import Flapjack.Pancake.Proofs.PanStructs.CompileExpOperators
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCmpShift
import Flapjack.Pancake.Proofs.PanStructs.CompileExpLoadByte
import Flapjack.Pancake.Proofs.PanStructs.CompileExpLoad32
import Flapjack.Pancake.Proofs.PanStructs.CompileExpLoad
import Flapjack.Pancake.Proofs.PanStructs.CompileExpBytesInWord
import Flapjack.Pancake.Semantics.PanSem.EvalInd
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Whole faithful original expression correctness theorem: all seven source
premises and all three conclusions, assembled through the source-guarded evaluator
induction principle. No case IH or target-run assumption remains in its signature. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectExact {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expression : ExpHOL width) (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context expression = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context expression) = some (convertV value) := by
  let P : PanSemStateFiniteExact width σ → ExpHOL width → Prop :=
    fun source expression => ∀ value : ValueHOL width,
@PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs →
    oldExpShapeExact context expression = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context expression) = some (convertV value)
  have hall : ∀ source expression, P source expression := by
    apply Flapjack.Pancake.Semantics.PanSem.EvalInd.evalIndExact P
    · intro s word v hv
      exact CompileExpAtomic.compileExpCorrectConst s context word v hv
    · intro s name v hv
      exact CompileExpVar.compileExpCorrectVar s context .local name v hv
    · intro s name v hv
      exact CompileExpVar.compileExpCorrectVar s context .global name v hv
    · intro s es ih v hv
      exact CompileExpRStruct.compileExpCorrectRStruct s context es v (fun a hm => ih a hm) hv
    · intro s index e ih v hv
      exact CompileExpRField.compileExpCorrectRField s context index e v ih hv
    · intro s name fields ih v hv
      apply CompileExpNStruct.compileExpCorrectNStruct s context name fields v ?_ hv
      intro info hlookup hnames a hm
      apply ih (fields.map Prod.fst) (fields.map Prod.snd) info
        (info.fields.map Prod.fst) (info.fields.map Prod.snd) a
      · simp [List.unzip_eq_map]
      · have heq : ∀ structs : StructContextExact,
            structs.findSome? (fun entry => if entry.1 = name then some entry.2 else none) =
              structContextLookupHOL name structs := by
          intro structs
          induction structs with
          | nil => rfl
          | cons entry rest ih =>
            rcases entry with ⟨candidate, info⟩
            by_cases hc : candidate = name
            · simp [List.findSome?, structContextLookupHOL, hc]
            · simp [List.findSome?, structContextLookupHOL, hc, Ne.symm hc, ih]
        rw [heq]
        exact hlookup
      · simp [List.unzip_eq_map]
      · exact hnames
      · exact hm
    · intro s name e ih v hv
      exact CompileExpNField.compileExpCorrectNField s context name e v ih hv
    · intro s shape address ih v hv
      exact CompileExpLoad.compileExpCorrectLoad s context shape address v ih hv
    · intro s address ih v hv
      exact CompileExpLoad32.compileExpCorrectLoad32 s context address v ih hv
    · intro s address ih v hv
      exact CompileExpLoadByte.compileExpCorrectLoadByte s context address v ih hv
    · intro s operator es ih v hv
      exact CompileExpOperators.compileExpCorrectOp s context operator es v (fun a hm => ih a hm) hv
    · intro s operator es ih v hv
      exact CompileExpOperators.compileExpCorrectPanop s context operator es v (fun a hm => ih a hm) hv
    · intro s operator left right ih v hv
      exact CompileExpCmpShift.compileExpCorrectCmp s context operator left right v ih.1 ih.2 hv
    · intro s operator left right ih v hv
      exact CompileExpCmpShift.compileExpCorrectShift s context operator left right v ih.1 ih.2 hv
    · intro s v hv
      exact CompileExpAtomic.compileExpCorrectBaseAddr s context v hv
    · intro s v hv
      exact CompileExpAtomic.compileExpCorrectTopAddr s context v hv
    · intro s v hv
      exact CompileExpBytesInWord.compileExpCorrectBytesInWord s context v hv
  exact hall source expression value h
end Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
