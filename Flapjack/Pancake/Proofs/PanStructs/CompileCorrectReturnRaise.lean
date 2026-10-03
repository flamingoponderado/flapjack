import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectReturnRaise
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


/-- Genuine Return case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectReturn {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.return expression : ProgHOL width) = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context (.return expression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return] at heval
  cases hv : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expression with
  | none =>
    rw [hv] at heval
    simp only [Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some value =>
    rw [hv] at heval
    dsimp only at heval
    split at heval
    · rename_i hsize
      simp only [Prod.mk.injEq] at heval
      rcases heval with ⟨hr, hp⟩
      subst res
      subst post
      have hexp := CompileExpCorrectExact.compileExpCorrectExact source context expression value
        ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hv,
          hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
      have hwf := @evalHOLExact_isWfShapeValueHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) hwlocal hwglobal expression value hv
      have hshape := ValueShapeConversion.shapeOfConvertVRev source.structs value ⟨hexp.2.1, hwf, hinfo⟩
      have hsizeConverted : sizeOfShapeWithContextHOL [] (shapeOfHOLExact (convertV value)) ≤ 32 := by
        rw [hshape, sizeOfCompileShape source.structs _
          ⟨isWfShapeValueHOLExact_shapeOfHOLExact source.structs value hwf, hinfo⟩]
        exact hsize
      refine ⟨?_, ?_, hglobal, hglobals, ?_, ?_, ?_⟩
      · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_return]
        have htarget := hexp.2.2
        simp only [PanSemStateFiniteExact.evalHOLFinite] at htarget
        rw [htarget]
        simp [convertResHOL, convertStateExact, PanSemStateFiniteExact.emptyLocalsHOLFinite,
          hsizeConverted, HolFiniteMapExact.map2]
      · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite, feveryHOL]
      · simp [isContResHOL]
      · simpa [resVsHOL, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hexp.2.1
      · simpa [resVsHOL, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hwf
    · simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
/-- Genuine Raise case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectRaise {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (exceptionId : MlS) (expression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.raise exceptionId expression : ProgHOL width) = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context (.raise exceptionId expression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise] at heval
  cases hs : source.eshapes.lookup exceptionId with
  | none =>
    simp only [hs] at heval
    cases hv : @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) expression <;>
      simp only [Prod.mk.injEq] at heval <;>
      exact False.elim (herror heval.1.symm)
  | some shape =>
    simp only [hs] at heval
    cases hv : @evalHOLExact width σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) expression with
    | none =>
      rw [hv] at heval
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | some value =>
      rw [hv] at heval
      dsimp only at heval
      split at heval
      · rename_i hcondition
        simp only [Prod.mk.injEq] at heval
        rcases heval with ⟨hr, hp⟩
        subst res
        subst post
        have hexp := CompileExpCorrectExact.compileExpCorrectExact source context expression value
          ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hv,
            hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
        have hwf := @evalHOLExact_isWfShapeValueHOLExact width σ _ source.toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) hwlocal hwglobal expression value hv
        have hshape := ValueShapeConversion.shapeOfConvertVRev source.structs value ⟨hexp.2.1, hwf, hinfo⟩
        have hsizeConverted : sizeOfShapeWithContextHOL [] (shapeOfHOLExact (convertV value)) ≤ 32 := by
          rw [hshape, sizeOfCompileShape source.structs _
            ⟨isWfShapeValueHOLExact_shapeOfHOLExact source.structs value hwf, hinfo⟩]
          exact hcondition.2
        have hlookupTarget : (convertStateExact context source).eshapes.lookup exceptionId =
            some (compileShapeExact context.structs shape) := by
          simp [convertStateExact, convertEshapesExact, HolFiniteMapExact.map2, hs]
        have hconditionTarget : shapeOfHOLExact (convertV value) =
            compileShapeExact context.structs shape ∧
            sizeOfShapeWithContextHOL (convertStateExact context source).structs
              (shapeOfHOLExact (convertV value)) ≤ 32 := by
          constructor
          · rw [hstructs, hshape, hcondition.1]
          · simpa [convertStateExact] using hsizeConverted
        refine ⟨?_, ?_, hglobal, hglobals, ?_, ?_, ?_⟩
        · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_raise]
          have htarget := hexp.2.2
          simp only [PanSemStateFiniteExact.evalHOLFinite] at htarget
          rw [hlookupTarget, htarget]
          simp [convertResHOL, convertStateExact, PanSemStateFiniteExact.emptyLocalsHOLFinite,
            hconditionTarget, HolFiniteMapExact.map2]
          simpa only [hconditionTarget.1] using hsizeConverted
        · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite, feveryHOL]
        · simp [isContResHOL]
        · simpa [resVsHOL, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hexp.2.1
        · simpa [resVsHOL, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hwf
      · simp only [Prod.mk.injEq] at heval
        exact False.elim (herror heval.1.symm)

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectReturnRaise
