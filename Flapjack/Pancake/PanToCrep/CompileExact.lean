import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
Exact-carrier expression lowering from HOL `PanLang.ExpHOL` to `CrepExpHOL`.

This belongs beside the production compiler as an exact source-semantics
counterpart. The production compiler remains separate until a kernel-checked
bridge and the full exact `compile_def` slice route are completed.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

/-! This module owns the exact-context carrier used by its tagged compiler so
    the finite-support qualifier is local to the declaration's module. Its
    fields and word/name carriers are the same ones as
    `PanToCrepContextExact`; the broad form below exists only for the required
    canonical finite-support roundtrip witness. -/

structure CompileExpContextBroad (width : Nat) where
  varsLookup : MlS → Option (ShapeHOL × List Nat)
  varsFiniteSupport : ∃ keys : List MlS, ∀ key, varsLookup key ≠ none → key ∈ keys
  funcsLookup : MlS → Option (List (MlS × ShapeHOL) × ShapeHOL)
  funcsFiniteSupport : ∃ keys : List MlS, ∀ key, funcsLookup key ≠ none → key ∈ keys
  eidsLookup : MlS → Option (BitVec width)
  eidsFiniteSupport : ∃ keys : List MlS, ∀ key, eidsLookup key ≠ none → key ∈ keys
  vmax : Nat

/-- Flapjack-specific carrier mirror of the tagged `PanToCrepContextExact`.
    It owns the finite-map fields in this module so the compiler's finite-map
    qualifier can be validated alongside its canonical witness. -/
structure CompileExpContextExact (width : Nat) [NeZero width] where
  vars : HolFiniteMapExact MlS (ShapeHOL × List Nat)
  funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL)
  eids : HolFiniteMapExact MlS (BitVec width)
  vmax : Nat

namespace CompileExpContextExact

def toBroad {width : Nat} [NeZero width] (context : CompileExpContextExact width) :
    CompileExpContextBroad width where
  varsLookup := context.vars.lookup
  varsFiniteSupport := context.vars.finiteSupport
  funcsLookup := context.funcs.lookup
  funcsFiniteSupport := context.funcs.finiteSupport
  eidsLookup := context.eids.lookup
  eidsFiniteSupport := context.eids.finiteSupport
  vmax := context.vmax

def ofBroad {width : Nat} [NeZero width] (context : CompileExpContextBroad width) :
    CompileExpContextExact width where
  vars := ⟨context.varsLookup, context.varsFiniteSupport⟩
  funcs := ⟨context.funcsLookup, context.funcsFiniteSupport⟩
  eids := ⟨context.eidsLookup, context.eidsFiniteSupport⟩
  vmax := context.vmax

/-- Canonical `HolFiniteMapExact` roundtrip required by the context qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) : ofBroad (toBroad context) = context := by
  cases context
  rfl

end CompileExpContextExact

/-! ### Exact-carrier `compile_exp_def`

The function below uses the HOL `ExpHOL`/`ShapeHOL` syntax, the finite-support
`PanToCrepContextExact`, and `CrepExpHOL` at the same positive word width. Its
equations follow `pan_to_crepScript.sml:39-101`: local lookup reads the exact
finite map; `compFieldHOL` and `loadShapeBytesHOLW` implement the cited HOL
helpers; and the bytes-in-word constant is `n2w (width DIV 8)`. This exact
definition does not by itself route the production compiler through the exact
carriers; that bridge remains tracked under the parent compile_def bead. -/

mutual
  /-- Exact width-indexed port of HOL `pan_to_crep$compile_exp_def`.
      `ShapeHOL`, `MlS`, and `CrepExpHOL width` preserve HOL's carriers and
      every fallback equation. -/
  @[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"
    (fmap_as_finite_support := [vars, funcs, eids])]
  def compileExpExactHOLW {width : Nat} [NeZero width]
      (context : CompileExpContextExact width) :
      Flapjack.Pancake.PanLang.ExpHOL width →
        List (CrepExpHOL width) × Flapjack.Pancake.PanLang.ShapeHOL
    | .const value => ([.const value], .one)
    | .var .local name =>
        match context.vars.lookup name with
        | some (shape, names) => (names.map .var, shape)
        | none => ([.const (0 : BitVec width)], .one)
    | .var .global _ => ([.const (0 : BitVec width)], .one)
    | .rstruct expressions =>
        let compiled := compileExpExactHOLWList context expressions
        (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
    | .rfield index expression =>
        let compiled := compileExpExactHOLW context expression
        match compiled.2 with
        | .comb shapes => compFieldHOL index shapes compiled.1
        | _ => ([.const (0 : BitVec width)], .one)
    | .nstruct _ _ => ([.const (0 : BitVec width)], .one)
    | .nfield _ _ => ([.const (0 : BitVec width)], .one)
    | .load shape expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, _) =>
            (loadShapeBytesHOLW (0 : BitVec width)
              (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) address, shape)
        | ([], _) => ([.const (0 : BitVec width)], .one)
    | .load32 expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, .one) => ([.load32 address], .one)
        | _ => ([.const (0 : BitVec width)], .one)
    | .loadByte expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, .one) => ([.loadByte address], .one)
        | _ => ([.const (0 : BitVec width)], .one)
    | .op operator expressions =>
        match cexpHeads (compileExpExactHOLWList context expressions |>.map Prod.fst) with
        | some expressions => ([.op operator expressions], .one)
        | none => ([.const (0 : BitVec width)], .one)
    | .panop operator expressions =>
        match cexpHeads (compileExpExactHOLWList context expressions |>.map Prod.fst) with
        | some expressions => ([.crepOp (compilePanOp operator) expressions], .one)
        | none => ([.const (0 : BitVec width)], .one)
    | .cmp operator left right =>
        match compileExpExactHOLW context left, compileExpExactHOLW context right with
        | (left :: _, _), (right :: _, _) => ([.cmp operator left right], .one)
        | _, _ => ([.const (0 : BitVec width)], .one)
    | .shift operator left right =>
        match compileExpExactHOLW context left, compileExpExactHOLW context right with
        | (left :: _, _), (right :: _, _) => ([.shift operator left right], .one)
        | _, _ => ([.const (0 : BitVec width)], .one)
    | .baseAddr => ([.baseAddr], .one)
    | .topAddr => ([.topAddr], .one)
    | .bytesInWord => ([.const (BitVec.ofNat width (width / 8))], .one)
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- `MAP (compile_exp ctxt)` in HOL's RStruct/Op/Panop equations. -/
  def compileExpExactHOLWList {width : Nat} [NeZero width]
      (context : CompileExpContextExact width) :
      List (Flapjack.Pancake.PanLang.ExpHOL width) →
        List (List (CrepExpHOL width) × Flapjack.Pancake.PanLang.ShapeHOL)
    | [] => []
    | expression :: expressions =>
        compileExpExactHOLW context expression ::
          compileExpExactHOLWList context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

end Flapjack
