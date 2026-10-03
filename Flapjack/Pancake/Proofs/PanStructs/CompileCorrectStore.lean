import Flapjack.Pancake.Proofs.PanStructs.FlattenConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectStore
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


/-- Genuine general Store case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectStore {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (destination valueExpression : ExpHOL width)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.store destination valueExpression : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.store destination valueExpression : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store] at heval
  cases hd : @evalHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) destination with
  | none =>
    rw [hd] at heval
    simp only [Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some destValue =>
    rw [hd] at heval
    cases destValue with
    | rStruct fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | nStruct name fields =>
      simp only [Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | val payload =>
      cases payload with
      | word address =>
        cases hs : @evalHOLExact width σ _ source.toExact
            (fun a => Classical.propDecidable (source.memaddrs a)) valueExpression with
        | none =>
          rw [hs] at heval
          simp only [Prod.mk.injEq] at heval
          exact False.elim (herror heval.1.symm)
        | some value =>
          rw [hs] at heval
          cases hm : @panMemStoresHOL width _ address (flattenHOL value) source.memaddrs
              (fun a => Classical.propDecidable (source.memaddrs a)) source.memory with
          | none =>
            simp only [hm, Prod.mk.injEq] at heval
            exact False.elim (herror heval.1.symm)
          | some memory =>
            simp only [hm, Prod.mk.injEq] at heval
            rcases heval with ⟨hr, hp⟩
            subst res
            subst post
            have hdexp := CompileExpCorrectExact.compileExpCorrectExact source context destination (.val (.word address))
              ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hd,
                hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
            have hsexp := CompileExpCorrectExact.compileExpCorrectExact source context valueExpression value
              ⟨by simpa [PanSemStateFiniteExact.evalHOLFinite] using hs,
                hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩
            have hdtarget := hdexp.2.2
            have hstarget := hsexp.2.2
            simp only [PanSemStateFiniteExact.evalHOLFinite, convertV] at hdtarget
            simp only [PanSemStateFiniteExact.evalHOLFinite] at hstarget
            refine ⟨?_, hlocal, hglobal, hglobals, ?_, ?_, ?_⟩
            · simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_store]
              rw [hdtarget, hstarget]
              dsimp only
              have hmTarget : @panMemStoresHOL width _ address (flattenHOL (convertV value))
                  (convertStateExact context source).memaddrs
                  (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
                  (convertStateExact context source).memory = some memory := by
                rw [FlattenConversion.flattenConvertV]
                exact hm
              rw [hmTarget]
              rfl
            · intro _
              exact hlocals
            · simp [resVsHOL]
            · simp [resVsHOL]

end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectStore
