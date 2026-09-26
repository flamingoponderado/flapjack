import Flapjack.Pancake.PanToCrep.CompileExact

/-!
Codec bridge between the tagged exact `compile_exp_def` port
(`compileExpExactHOLW` over `ExpHOL`/`CrepExpHOL`/`ShapeHOL`) and the executed
production expression compiler `compileExpHOL` (over production `Exp`/`CrepExp`).

This module is untagged Flapjack infrastructure: it connects the reviewed exact
port to the executed pass and is the expression-level part of the exact
`code_rel` boundary. The compiler expression on the production side is reached
through a `PanToCrepHOLContext` induced from the exact finite-map context by
`CompileExpContextExact.prodContext`; names are decoded with `ofString`, and the
shape is decoded with `shapeOfHOL`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

namespace CompileExpContextExact

/-- Production finite-map context induced by an exact compile context. The
    production side is a function-backed `FiniteMap` keyed by `String`; every
    name is encoded with `ofString` and the stored `ShapeHOL` is decoded with
    `shapeOfHOL`. `funcs`/`eids` are never read by `compileExpHOL`. -/
def prodContext {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    PanToCrepHOLContext (BitVec width) where
  vars := fun name =>
    (context.vars.lookup (ofString name)).map
      (fun entry => (shapeOfHOL entry.1, entry.2))
  funcs := fun _ => none
  eids := fun _ => none
  vmax := context.vmax

end CompileExpContextExact

/-- Codec agreement between the production and exact expression compilers at a
    single expression. The first component is the compiled expression list
    (production mapped forward by `crepExpToHOL`) and the second the result
    shape (`shapeToHOL` of the production shape). -/
def compileExpBridgeProp {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width)) :
    Prop :=
  (compileExpHOL (CompileExpContextExact.prodContext context) expression).1.map
      crepExpToHOL
    = (compileExpExactHOLW context (expToHOL expression)).1
  ∧ shapeToHOL
      (compileExpHOL (CompileExpContextExact.prodContext context) expression).2
    = (compileExpExactHOLW context (expToHOL expression)).2

/-- Codec agreement for the mutually recursive argument list. -/
def compileExpListBridgeProp {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (expressions : List (Exp (BitVec width))) : Prop :=
  (compileExpHOL.compileExpListHOL
      (CompileExpContextExact.prodContext context) expressions).map
        (fun p => (p.1.map crepExpToHOL, shapeToHOL p.2))
    = compileExpExactHOLWList context (expressions.map expToHOL)

/-! ### Leaf cases

These are the `compile_exp` clauses with no recursive sub-expression: `Const`,
`Var` (local/global), `NStruct`, `NField`, `BaseAddr`, `TopAddr` and
`BytesInWord`. Each is a standalone handler lemma for the eventual
`Flapjack.Exp.rec` assembly. -/

theorem compileExpBridge_const {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (value : BitVec width) :
    compileExpBridgeProp context (.const value) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_1,
    compileExpExactHOLW.eq_1, expToHOL.eq_1]
  constructor <;>
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]

theorem compileExpBridge_var {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (kind : VarKind) (name : VarName) :
    compileExpBridgeProp context (.var kind name) := by
  cases kind
  · simp only [compileExpBridgeProp, compileExpHOL.eq_2,
      compileExpExactHOLW.eq_2, expToHOL.eq_2]
    cases h : context.vars.lookup (ofString name) with
    | none =>
        simp only [CompileExpContextExact.prodContext, h, FLOOKUP,
          Option.map_none, List.map_cons, List.map_nil, crepExpToHOL.eq_1,
          shapeToHOL]
        constructor <;> trivial
    | some entry =>
        obtain ⟨shape, names⟩ := entry
        simp only [CompileExpContextExact.prodContext, h, FLOOKUP,
          Option.map_some, shapeToHOL_shapeOfHOL]
        constructor
        · rw [List.map_map]
          apply List.map_congr_left
          intro n _
          simp only [Function.comp_apply]
          exact crepExpToHOL.eq_2 n
        · trivial
  · simp only [compileExpBridgeProp, compileExpHOL.eq_3,
      compileExpExactHOLW.eq_3, expToHOL.eq_2]
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
    constructor <;> trivial

theorem compileExpBridge_nStruct {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : StructName)
    (fields : List (FieldName × Exp (BitVec width))) :
    compileExpBridgeProp context (.nStruct name fields) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_6,
    compileExpExactHOLW.eq_6, expToHOL.eq_5]
  constructor <;>
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]

theorem compileExpBridge_nField {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : FieldName)
    (value : Exp (BitVec width)) :
    compileExpBridgeProp context (.nField name value) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_7,
    compileExpExactHOLW.eq_7, expToHOL.eq_6]
  constructor <;>
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]

theorem compileExpBridge_baseAddr {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    compileExpBridgeProp context (.baseAddr) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_15,
    compileExpExactHOLW.eq_15, expToHOL.eq_14]
  constructor <;>
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_11, shapeToHOL]

theorem compileExpBridge_topAddr {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    compileExpBridgeProp context (.topAddr) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_16,
    compileExpExactHOLW.eq_16, expToHOL.eq_15]
  constructor <;>
    simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_12, shapeToHOL]

theorem compileExpBridge_bytesInWord {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    compileExpBridgeProp context (.bytesInWord) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_17,
    compileExpExactHOLW.eq_17, expToHOL.eq_16]
  constructor
  · first | rfl |
      (simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]; rfl)
  · first | rfl | simp only [shapeToHOL]

end Flapjack
