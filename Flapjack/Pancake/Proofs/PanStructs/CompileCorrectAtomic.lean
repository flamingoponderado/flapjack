import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAtomic
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


/-- Genuine Skip case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectSkip {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.skip : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.skip : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  rcases h with ⟨heval, _, hlocal, hglobal, _, _, _, hlocals, hglobals, _⟩
  simp only [PanSemStateFiniteExact.evaluateHOLFiniteState_skip, Prod.mk.injEq] at heval
  rcases heval with ⟨hr, hp⟩
  subst res
  subst post
  refine ⟨?_, hlocal, hglobal, hglobals, ?_, ?_, ?_⟩
  · simp [compileProgExact, convertResHOL]
  · intro _
    exact hlocals
  · simp [resVsHOL]
  · simp [resVsHOL]

/-- Genuine Break case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectBreak {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.break : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.break : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  rcases h with ⟨heval, _, hlocal, hglobal, _, _, _, hlocals, hglobals, _⟩
  simp only [PanSemStateFiniteExact.evaluateHOLFiniteState_break, Prod.mk.injEq] at heval
  rcases heval with ⟨hr, hp⟩
  subst res
  subst post
  refine ⟨?_, hlocal, hglobal, hglobals, ?_, ?_, ?_⟩
  · simp [compileProgExact, convertResHOL]
  · intro _
    exact hlocals
  · simp [resVsHOL]
  · simp [resVsHOL]

/-- Genuine Continue case of the full original program theorem. All ten source
premises and all seven conclusions are retained; this leaf has no recursive IH. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectContinue {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.continue : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.continue : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  rcases h with ⟨heval, _, hlocal, hglobal, _, _, _, hlocals, hglobals, _⟩
  simp only [PanSemStateFiniteExact.evaluateHOLFiniteState_continue, Prod.mk.injEq] at heval
  rcases heval with ⟨hr, hp⟩
  subst res
  subst post
  refine ⟨?_, hlocal, hglobal, hglobals, ?_, ?_, ?_⟩
  · simp [compileProgExact, convertResHOL]
  · intro _
    exact hlocals
  · simp [resVsHOL]
  · simp [resVsHOL]
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAtomic
