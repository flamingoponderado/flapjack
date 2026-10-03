import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Proofs.PanStructs.ConvertState
import Flapjack.Pancake.Proofs.PanStructs.ShapeMap
import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
import Flapjack.Pancake.PanStructs.CompileDeclsExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectNilName
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


/-- Flapjack fixed induction-property encoding; no separate HOL declaration.
It quantifies all post states/contexts/compiled declarations of the original
declaration theorem, rather than letting callers supply a predicate. -/
def DeclsProperty {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (declarations : List (DeclHOL width)) : Prop :=
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) declarations = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context declarations = (compiled, finalContext)) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ (convertStateExact finalContext source)
      (fun address => Classical.propDecidable ((convertStateExact finalContext source).memaddrs address))
      compiled = some (convertStateExact finalContext post) ∧
    (∃ globals, finalContext = { context with globals := globals } ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) post.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) post.globals ∧
      post.structs = source.structs ∧ post.locals = source.locals ∧
      shapeMap globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2))
/-- Original Nil minor: all eight hypotheses, actual target declaration run
and full existential globals/context/fields/WF/structs/locals/shape-map result.
No IH or target-result premise is used. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectNil {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) ([] : List (DeclHOL width)) = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context ([] : List (DeclHOL width)) = (compiled, finalContext)) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ (convertStateExact finalContext source)
      (fun address => Classical.propDecidable ((convertStateExact finalContext source).memaddrs address))
      compiled = some (convertStateExact finalContext post) ∧
    (∃ globals, finalContext = { context with globals := globals } ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) post.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) post.globals ∧
      post.structs = source.structs ∧ post.locals = source.locals ∧
      shapeMap globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2)) := by
  intro post context finalContext compiled h
  rcases h with ⟨heval, _, _, _, hfields, hwf, hmap, hcompile⟩
  simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite, Option.some.injEq] at heval
  subst post
  simp only [compileDeclsExact, Prod.mk.injEq] at hcompile
  rcases hcompile with ⟨hcompiled, hcontext⟩
  subst compiled
  subst finalContext
  exact ⟨rfl, context.globals, rfl, hfields, hwf, rfl, rfl, hmap⟩
/-- Original Name minor with precisely the unguarded same-state tail IH.
Both source declaration evaluation and compilation remove Name; full original
hypotheses and existential conclusion are retained without extra premises. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectName {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS)
    (fields : List (MlS × ShapeHOL)) (declarations : List (DeclHOL width))
    (ih : DeclsProperty source declarations) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) (.name name fields :: declarations) = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context (.name name fields :: declarations) = (compiled, finalContext)) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ (convertStateExact finalContext source)
      (fun address => Classical.propDecidable ((convertStateExact finalContext source).memaddrs address))
      compiled = some (convertStateExact finalContext post) ∧
    (∃ globals, finalContext = { context with globals := globals } ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) post.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) post.globals ∧
      post.structs = source.structs ∧ post.locals = source.locals ∧
      shapeMap globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2)) := by
  intro post context finalContext compiled h
  apply ih post context finalContext compiled
  simpa only [PanSemStateFiniteExact.evaluateDeclsHOLFinite, compileDeclsExact] using h
end Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectNilName
