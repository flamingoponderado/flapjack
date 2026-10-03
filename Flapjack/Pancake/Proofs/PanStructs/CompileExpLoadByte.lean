import Flapjack.Pancake.Proofs.PanStructs.CompileExpOperators
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpLoadByte
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

/-- Genuine LoadByte case retaining the original full child induction hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectLoadByte {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expression : ExpHOL width) (value : ValueHOL width)
    (ih : ∀ childValue : ValueHOL width,
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
        (fun a => Classical.propDecidable (source.memaddrs a)) (.loadByte expression : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.loadByte expression : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.loadByte expression : ExpHOL width)) = some (convertV value) := by
  classical
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
  have hr := heval
  simp only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
    PanSemStateFiniteExact.toExact] at hr
  split at hr
  · rename_i word hchild
    cases hm : panMemLoadByteHOL source.memory source.memaddrs source.be word with
    | none => simp [hm] at hr
    | some byte =>
      have hv : ValueHOL.val (.word (BitVec.ofNat width byte.toNat)) = value := by
        simpa [hm] using hr
      subst value
      obtain ⟨_, _, htarget⟩ := ih (.val (.word word))
        ⟨hchild, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      simp only [PanSemStateFiniteExact.evalHOLFinite, convertV] at htarget
      refine ⟨?_, ?_, ?_⟩
      · simp [oldExpShapeExact, shapeOfHOLExact]
      · simp [valueFldsOkHOLExact]
      · simp only [compileExpExact, PanSemStateFiniteExact.evalHOLFinite, evalHOLExact]
        rw [htarget]
        simp only [convertStateExact, convertV]
        exact congrArg (Option.map (fun value => ValueHOL.val (.word (BitVec.ofNat width value.toNat)))) hm
  · simp at hr
end Flapjack.Pancake.Proofs.PanStructs.CompileExpLoadByte
