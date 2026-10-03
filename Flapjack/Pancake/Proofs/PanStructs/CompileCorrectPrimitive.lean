import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAssign
import Flapjack.Pancake.Proofs.PanStructs.CompileExpMmapHelper
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.PanStructs.CompileProgExact
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectPrimitive
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


/-- Genuine Primitive case of the full original program theorem, with all ten
premises and seven conclusions and no recursive IH. The source-success primitive
returns the original AddCarry two-word RStruct. Full expression correctness and
mmap preservation supply the actual target argument run. For the local update,
an internally constructed two-constant RStruct expression has precisely the same
source and compiled target value; applying the full Assign case proves its actual
validity/update obligations and all postconditions. This internal expression adds
no premise and changes neither source nor target evaluator. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectPrimitive {width : Nat} {σ : Type} [NeZero width]
    (source post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (name : MlS) (operator : PrimOp) (expressions : List (ExpHOL width))
    (res : Option (PanSemResultExact width))
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState source (.primitive name operator expressions : ProgHOL width) = (res, post) ∧
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
      (compileProgExact context (.primitive name operator expressions : ProgHOL width)) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  classical
  rcases h with ⟨heval, hstructs, hlocal, hglobal, hwlocal, hwglobal, hinfo, hlocals, hglobals, herror⟩
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_primitive] at heval
  cases hv : @evalListHOLExact width σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) expressions with
  | none =>
    simp only [hv, Prod.mk.injEq] at heval
    exact False.elim (herror heval.1.symm)
  | some values =>
    rw [hv] at heval
    dsimp only at heval
    cases hp : panPrimopHOLExact operator values with
    | none =>
      simp only [hp, Prod.mk.injEq] at heval
      exact False.elim (herror heval.1.symm)
    | some value =>
      rw [hp] at heval
      dsimp only at heval
      have hlist := CompileExpMmapHelper.compileExpCorrectMmapHelper source context expressions values
        ⟨hv, by
          intro expression hmem val hex
          exact (CompileExpCorrectExact.compileExpCorrectExact source context expression val
            ⟨hex, hlocals, hglobals, hstructs, hlocal, hglobal, hinfo⟩).2.2⟩
      change evalListHOLExact (convertStateExact context source).toExact
        (compileExpsExact context expressions) = some (values.map convertV) at hlist
      unfold panPrimopHOLExact at hp
      split at hp
      next left right carry =>
        simp only [Option.some.injEq] at hp
        subst value
        let literal : ExpHOL width := .rstruct
          [.const (wordAddCarryHOL left right carry).1, .const (wordAddCarryHOL left right carry).2]
        have hassign : PanSemStateFiniteExact.evaluateHOLFiniteState source
            (.assign .local name literal) = (res,post) := by
          rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
          simpa only [literal, evalHOLExact, evalListHOLExact, Option.bind_some,
            Option.map_some, PanSemStateFiniteExact.setKvarHOLFinite] using heval
        have ha := CompileCorrectAssign.compileCorrectAssign source post context .local name literal res
          ⟨hassign,hstructs,hlocal,hglobal,hwlocal,hwglobal,hinfo,hlocals,hglobals,herror⟩
        refine ⟨?_,ha.2⟩
        have ht := ha.1
        simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_assign,
          literal, compileExpExact, compileExpsExact, evalHOLExact, evalListHOLExact,
          Option.map_some, PanSemStateFiniteExact.setKvarHOLFinite] at ht
        simp only [compileProgExact, PanSemStateFiniteExact.evaluateHOLFiniteState_primitive]
        rw [hlist]
        simpa only [List.map_cons, List.map_nil, convertV, panPrimopHOLExact] using ht
      next => simp at hp
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectPrimitive
