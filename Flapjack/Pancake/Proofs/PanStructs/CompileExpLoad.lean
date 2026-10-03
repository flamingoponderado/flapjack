import Flapjack.Pancake.Proofs.PanStructs.CompileExpAtomic
import Flapjack.Pancake.Proofs.PanStructs.MemLoadConversion
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpLoad
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

/-- Genuine `Load` case of the original `compile_exp_correct`
(`pan_structsProofScript.sml:740-748`), retaining the original full child
induction hypothesis under the original `eval_ind` Load guard
(`is_wf_shape s.structs shape ==> P s address`), and all seven premises and
three conclusions. As in the
source, the loaded value is converted by `mem_load_conversion_inst`, and the
compiled shape is name-free by `compile_shape_no_name`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectLoad {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (shape : ShapeHOL) (expression : ExpHOL width) (value : ValueHOL width)
    (ih : isWfShapeExactHOL source.structs shape = true → ∀ childValue : ValueHOL width,
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) expression = some childValue ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs →
   oldExpShapeExact context expression = shapeOfHOLExact childValue ∧
    valueFldsOkHOLExact source.structs childValue = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context expression) = some (convertV childValue))
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a))
        (.load shape expression : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.load shape expression : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.load shape expression : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
    PanSemStateFiniteExact.toExact] at hr
  split at hr
  · rename_i hwf
    split at hr
    · rename_i word hchild
      obtain ⟨_, _, htarget⟩ := ih hwf (.val (.word word))
        ⟨hchild, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      simp only [PanSemStateFiniteExact.evalHOLFinite, convertV] at htarget
      obtain ⟨hconv, hflds⟩ := memLoadConversionInst source.memaddrs source.memory source.structs
        shape word value ⟨hr, hwf, hinfo⟩
      refine ⟨?_, hflds, ?_⟩
      · simp only [oldExpShapeExact]
        exact ((memLoadHOLExact_shape_eq (width := width)).1 shape word _ _ _ value hr).symm
      · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]
        rw [htarget]
        simp only [convertStateExact]
        rw [hstructs]
        simp only [compileShapeNoName, if_true]
        exact hconv
    · simp at hr
  · simp at hr
end Flapjack.Pancake.Proofs.PanStructs.CompileExpLoad
