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


/-! ### List-motive consequences and the `RStruct` handler

Generic list lemmas push `crepExpToHOL`/`shapeToHOL` through the pair map used by
`compileExpListBridgeProp`; the `RStruct` handler is the first recursive case of
the bridge. -/

theorem map_flatMap_fst {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (entries : List (List α × γ)) :
    (entries.flatMap Prod.fst).map f =
      (entries.map (fun entry => (entry.1.map f, g entry.2))).flatMap Prod.fst := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.map_append, ih]

theorem map_map_snd {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (entries : List (List α × γ)) :
    (entries.map Prod.snd).map g =
      (entries.map (fun entry => (entry.1.map f, g entry.2))).map Prod.snd := by
  rw [List.map_map, List.map_map]
  rfl

theorem compileExpListBridgeProp_fstMap {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (expressions : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context expressions) :
    ((compileExpHOL.compileExpListHOL
        (CompileExpContextExact.prodContext context) expressions).map
          Prod.fst).map (List.map crepExpToHOL)
      = (compileExpExactHOLWList context (expressions.map expToHOL)).map
          Prod.fst := by
  unfold compileExpListBridgeProp at h
  rw [← h]
  rw [List.map_map, List.map_map]
  rfl

theorem compileExpListBridgeProp_sndMap {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (expressions : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context expressions) :
    ((compileExpHOL.compileExpListHOL
        (CompileExpContextExact.prodContext context) expressions).map
          Prod.snd).map shapeToHOL
      = (compileExpExactHOLWList context (expressions.map expToHOL)).map
          Prod.snd := by
  unfold compileExpListBridgeProp at h
  rw [← h]
  rw [List.map_map, List.map_map]
  rfl

theorem compileExpListBridgeProp_fstFlatMap {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (expressions : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context expressions) :
    ((compileExpHOL.compileExpListHOL
        (CompileExpContextExact.prodContext context) expressions).flatMap
          Prod.fst).map crepExpToHOL
      = (compileExpExactHOLWList context (expressions.map expToHOL)).flatMap
          Prod.fst := by
  unfold compileExpListBridgeProp at h
  rw [map_flatMap_fst crepExpToHOL shapeToHOL]
  rw [h]

theorem compileExpBridge_rStruct {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (fields : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context fields) :
    compileExpBridgeProp context (.rStruct fields) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_4, compileExpExactHOLW.eq_4,
    expToHOL.eq_3]
  constructor
  · exact compileExpListBridgeProp_fstFlatMap context fields h
  · simp only [shapeToHOL]
    exact congrArg ShapeHOL.comb (compileExpListBridgeProp_sndMap context fields h)

theorem compileExpListBridgeProp_nil {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    compileExpListBridgeProp context ([] : List (Exp (BitVec width))) := by
  simp only [compileExpListBridgeProp, List.map_nil,
    compileExpHOL.compileExpListHOL.eq_1, compileExpExactHOLWList.eq_1]

theorem compileExpListBridgeProp_cons {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (head : Exp (BitVec width))
    (tail : List (Exp (BitVec width)))
    (hhead : compileExpBridgeProp context head)
    (htail : compileExpListBridgeProp context tail) :
    compileExpListBridgeProp context (head :: tail) := by
  unfold compileExpBridgeProp at hhead
  unfold compileExpListBridgeProp at htail ⊢
  simp only [List.map_cons, compileExpHOL.compileExpListHOL.eq_2,
    compileExpExactHOLWList.eq_2]
  rw [htail]
  congr 1
  exact Prod.ext hhead.1 hhead.2

end Flapjack
