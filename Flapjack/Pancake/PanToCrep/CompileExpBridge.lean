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

/-- Production context induced by an exact compiler context. Retain all three
    decoded maps and `vmax`, so the expression codec's production side uses the
    same full context as the program-clause bridges. `compileExpHOL` reads only
    `vars` and `vmax`; preserving `funcs`/`eids` here therefore does not change
    its result. -/
def prodContext {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    PanToCrepHOLContext (BitVec width) := context.toProduction

/-- The pre-c9 expression adapter projected the exact context to `vars` and
    `vmax`, filling `funcs` and `eids` with empty maps. This focused kernel
    equality records that the old and full-context adapters produce the same
    output for local-variable expressions, the expression clause that reads
    the variable map. The recursive expression clauses are unchanged by c9;
    they call this same compiler recursively. -/
theorem compileExpHOL_oldProjection_localVar_eq {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : VarName) :
    compileExpHOL context.toProduction (.var .local name) =
      compileExpHOL
        { context.toProduction with funcs := fun _ => none, eids := fun _ => none }
        (.var .local name) := by
  simp [compileExpHOL.eq_2, FLOOKUP]

end CompileExpContextExact

private theorem stringOfBytes_byteRanged (name : MlS) :
    ∀ c ∈ toStringOfBytes name |>.toList, c.toNat < 256 := by
  intro c hc
  unfold toStringOfBytes at hc
  simp only [String.toList_ofList, List.mem_map] at hc
  rcases hc with ⟨b, _hb, rfl⟩
  rw [Flapjack.Basis.Pure.MlString.ofNat_toNat_char]
  have hlt : b.toNat < 256 := by
    have h := b.isLt
    omega
  exact hlt

private theorem shapeOfHOL_byteRanged :
    (shape : ShapeHOL) → ShapeByteRanged (shapeOfHOL shape)
  | .one => by simp [ShapeByteRanged, shapeOfHOL]
  | .named name => by
      simpa [ShapeByteRanged, shapeOfHOL] using stringOfBytes_byteRanged name
  | .comb fields => by
      simp only [shapeOfHOL, ShapeByteRanged]
      intro shape hshape
      obtain ⟨source, _hsource, rfl⟩ := List.mem_map.mp hshape
      exact shapeOfHOL_byteRanged source

private theorem expOfHOL_byteRanged {width : Nat} [NeZero width] :
    (expression : ExpHOL width) → ExpByteRanged (expOfHOL expression) :=
  ExpHOL.rec
    (motive_1 := fun expression => ExpByteRanged (expOfHOL expression))
    (motive_2 := fun expressions =>
      ListExpByteRanged (expressions.map expOfHOL))
    (motive_3 := fun fields =>
      ListFieldByteRanged (fields.map
        (fun p => (toStringOfBytes p.1, expOfHOL p.2))))
    (motive_4 := fun field =>
      (∀ c ∈ toStringOfBytes field.1 |>.toList, c.toNat < 256) ∧
        ExpByteRanged (expOfHOL field.2))
    (by simp [expOfHOL, ExpByteRanged])
    (fun _kind name => by
      simpa [expOfHOL, ExpByteRanged] using stringOfBytes_byteRanged name)
    (fun _fields ih => by simpa [expOfHOL, ExpByteRanged, ListExpByteRanged] using ih)
    (fun _index _value ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun name _fields ih => by
      simpa [expOfHOL, ExpByteRanged, ListFieldByteRanged] using
        And.intro (stringOfBytes_byteRanged name) ih)
    (fun name _value ih => by
      simpa [expOfHOL, ExpByteRanged] using
        And.intro (stringOfBytes_byteRanged name) ih)
    (fun shape _address ih => by
      simpa [expOfHOL, ExpByteRanged] using
        And.intro (shapeOfHOL_byteRanged shape) ih)
    (fun _address ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _address ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _args ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _args ih => by simpa [expOfHOL, ExpByteRanged] using ih)
    (fun _operator _left _right ihl ihr => by
      simpa [expOfHOL, ExpByteRanged] using And.intro ihl ihr)
    (fun _operator _left _right ihl ihr => by
      simpa [expOfHOL, ExpByteRanged] using And.intro ihl ihr)
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [expOfHOL, ExpByteRanged])
    (by simp [ListExpByteRanged])
    (fun _head _tail ihHead ihTail => by
      simpa [ListExpByteRanged, List.map] using And.intro ihHead ihTail)
    (by simp [ListFieldByteRanged])
    (fun _head _tail ihHead ihTail => by
      simpa [ListFieldByteRanged, List.map] using
        And.intro ihHead.1 (And.intro ihHead.2 ihTail))
    (fun fst snd ih => by
      exact ⟨stringOfBytes_byteRanged fst, ih⟩)

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
        simp only [CompileExpContextExact.prodContext,
          PanToCrepContextExact.toProduction, h, FLOOKUP,
          Option.map_none, List.map_cons, List.map_nil, crepExpToHOL.eq_1,
          shapeToHOL]
        constructor <;> trivial
    | some entry =>
        obtain ⟨shape, names⟩ := entry
        simp only [CompileExpContextExact.prodContext,
          PanToCrepContextExact.toProduction, h, FLOOKUP,
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


/-! ### `Op` and `PanOp` handlers

Both cases extract the argument heads with `cexpHeads`; the codec push-through
lemma `cexpHeads_map_crepExpToHOL` and the list-motive first-component bridge
`compileExpListBridgeProp_fstMap` align the production and exact scrutinees. -/

theorem compileExpBridge_op {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : BinOp)
    (arguments : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context arguments) :
    compileExpBridgeProp context (.op operator arguments) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_11, compileExpExactHOLW.eq_11,
    expToHOL.eq_10]
  have hf := compileExpListBridgeProp_fstMap context arguments h
  have heq :
      cexpHeads
          ((compileExpExactHOLWList context (arguments.map expToHOL)).map Prod.fst)
        = (cexpHeads
            ((compileExpHOL.compileExpListHOL
              (CompileExpContextExact.prodContext context) arguments).map
                Prod.fst)).map (List.map crepExpToHOL) := by
    rw [← hf]
    exact cexpHeads_map_crepExpToHOL _
  constructor
  · rw [heq]
    cases cexpHeads
        ((compileExpHOL.compileExpListHOL
          (CompileExpContextExact.prodContext context) arguments).map Prod.fst) with
    | none =>
        simp only [Option.map_none, List.map_cons, List.map_nil,
          crepExpToHOL.eq_1]
    | some es =>
        simp only [Option.map_some, List.map_cons, List.map_nil,
          crepExpToHOL.eq_7]
  · rw [heq]
    cases cexpHeads
        ((compileExpHOL.compileExpListHOL
          (CompileExpContextExact.prodContext context) arguments).map Prod.fst) with
    | none => simp only [Option.map_none, shapeToHOL]
    | some es => simp only [Option.map_some, shapeToHOL]

theorem compileExpBridge_panOp {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : PanOp)
    (arguments : List (Exp (BitVec width)))
    (h : compileExpListBridgeProp context arguments) :
    compileExpBridgeProp context (.panOp operator arguments) := by
  simp only [compileExpBridgeProp, compileExpHOL.eq_12, compileExpExactHOLW.eq_12,
    expToHOL.eq_11]
  have hf := compileExpListBridgeProp_fstMap context arguments h
  have heq :
      cexpHeads
          ((compileExpExactHOLWList context (arguments.map expToHOL)).map Prod.fst)
        = (cexpHeads
            ((compileExpHOL.compileExpListHOL
              (CompileExpContextExact.prodContext context) arguments).map
                Prod.fst)).map (List.map crepExpToHOL) := by
    rw [← hf]
    exact cexpHeads_map_crepExpToHOL _
  constructor
  · rw [heq]
    cases cexpHeads
        ((compileExpHOL.compileExpListHOL
          (CompileExpContextExact.prodContext context) arguments).map Prod.fst) with
    | none =>
        simp only [Option.map_none, List.map_cons, List.map_nil,
          crepExpToHOL.eq_1]
    | some es =>
        simp only [Option.map_some, List.map_cons, List.map_nil,
          crepExpToHOL.eq_8]
  · rw [heq]
    cases cexpHeads
        ((compileExpHOL.compileExpListHOL
          (CompileExpContextExact.prodContext context) arguments).map Prod.fst) with
    | none => simp only [Option.map_none, shapeToHOL]
    | some es => simp only [Option.map_some, shapeToHOL]


/-! ### Multi-subexpression and guarded-shape handlers

`cmp`/`shift` compile both subexpressions and inspect the head of each compiled
list; `load32`/`loadByte` compile one subexpression and additionally require the
exact `ShapeHOL.one` shape. In every case the production and exact matches are
aligned by rewriting the exact compiled pair with the codec pair equality
`Prod.ext` of the two conjuncts of `compileExpBridgeProp`. -/

theorem compileExpBridge_cmp {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : Cmp)
    (left right : Exp (BitVec width))
    (hleft : compileExpBridgeProp context left)
    (hright : compileExpBridgeProp context right) :
    compileExpBridgeProp context (.cmp operator left right) := by
  obtain ⟨hl1, hl2⟩ := hleft
  obtain ⟨hr1, hr2⟩ := hright
  have hexLeft :
      compileExpExactHOLW context (expToHOL left) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) left).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) left).2) :=
    Prod.ext hl1.symm hl2.symm
  have hexRight :
      compileExpExactHOLW context (expToHOL right) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) right).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) right).2) :=
    Prod.ext hr1.symm hr2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_13, compileExpExactHOLW.eq_13,
    expToHOL.eq_12, hexLeft, hexRight]
  constructor
  · cases compileExpHOL (CompileExpContextExact.prodContext context) left with
    | mk l1 l2 =>
      cases compileExpHOL (CompileExpContextExact.prodContext context) right with
      | mk r1 r2 =>
        cases l1 with
        | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
        | cons a as =>
          cases r1 with
          | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
          | cons b bs => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_9]
  · cases compileExpHOL (CompileExpContextExact.prodContext context) left with
    | mk l1 l2 =>
      cases compileExpHOL (CompileExpContextExact.prodContext context) right with
      | mk r1 r2 =>
        cases l1 <;> cases r1 <;> simp only [List.map_cons, List.map_nil, shapeToHOL]

theorem compileExpBridge_shift {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : Shift)
    (left right : Exp (BitVec width))
    (hleft : compileExpBridgeProp context left)
    (hright : compileExpBridgeProp context right) :
    compileExpBridgeProp context (.shift operator left right) := by
  obtain ⟨hl1, hl2⟩ := hleft
  obtain ⟨hr1, hr2⟩ := hright
  have hexLeft :
      compileExpExactHOLW context (expToHOL left) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) left).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) left).2) :=
    Prod.ext hl1.symm hl2.symm
  have hexRight :
      compileExpExactHOLW context (expToHOL right) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) right).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) right).2) :=
    Prod.ext hr1.symm hr2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_14, compileExpExactHOLW.eq_14,
    expToHOL.eq_13, hexLeft, hexRight]
  constructor
  · cases compileExpHOL (CompileExpContextExact.prodContext context) left with
    | mk l1 l2 =>
      cases compileExpHOL (CompileExpContextExact.prodContext context) right with
      | mk r1 r2 =>
        cases l1 with
        | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
        | cons a as =>
          cases r1 with
          | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
          | cons b bs => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_10]
  · cases compileExpHOL (CompileExpContextExact.prodContext context) left with
    | mk l1 l2 =>
      cases compileExpHOL (CompileExpContextExact.prodContext context) right with
      | mk r1 r2 =>
        cases l1 <;> cases r1 <;> simp only [List.map_cons, List.map_nil, shapeToHOL]

theorem compileExpBridge_load32 {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width))
    (h : compileExpBridgeProp context expression) :
    compileExpBridgeProp context (.load32 expression) := by
  obtain ⟨hl1, hl2⟩ := h
  have hex :
      compileExpExactHOLW context (expToHOL expression) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) expression).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :=
    Prod.ext hl1.symm hl2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_9, compileExpExactHOLW.eq_9,
    expToHOL.eq_8, hex]
  constructor
  · cases compileExpHOL (CompileExpContextExact.prodContext context) expression with
    | mk l1 l2 =>
      cases l1 with
      | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
      | cons a as =>
        cases l2 with
        | one => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_4, shapeToHOL]
        | comb fields =>
            simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
        | named nm =>
            simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
  · cases compileExpHOL (CompileExpContextExact.prodContext context) expression with
    | mk l1 l2 =>
      cases l1 <;> (cases l2 <;> simp only [List.map_cons, List.map_nil, shapeToHOL])

theorem compileExpBridge_loadByte {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width))
    (h : compileExpBridgeProp context expression) :
    compileExpBridgeProp context (.loadByte expression) := by
  obtain ⟨hl1, hl2⟩ := h
  have hex :
      compileExpExactHOLW context (expToHOL expression) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) expression).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :=
    Prod.ext hl1.symm hl2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_10, compileExpExactHOLW.eq_10,
    expToHOL.eq_9, hex]
  constructor
  · cases compileExpHOL (CompileExpContextExact.prodContext context) expression with
    | mk l1 l2 =>
      cases l1 with
      | nil => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1]
      | cons a as =>
        cases l2 with
        | one => simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_5, shapeToHOL]
        | comb fields =>
            simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
        | named nm =>
            simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
  · cases compileExpHOL (CompileExpContextExact.prodContext context) expression with
    | mk l1 l2 =>
      cases l1 <;> (cases l2 <;> simp only [List.map_cons, List.map_nil, shapeToHOL])


/-! ### Single-subexpression guarded handlers: `rField` and `load`

`rField` inspects the shape of the compiled subexpression, `load` additionally
guards on a nonempty compiled list. The production and exact matches are aligned
by the codec pair equality, `compileField_map_codecs`, and the checked
`loadShape`/`loadShapeBytes`/`loadShapeBytesHOLW` bridges. -/

theorem compileExpBridge_rField {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (index : Nat)
    (expression : Exp (BitVec width))
    (h : compileExpBridgeProp context expression) :
    compileExpBridgeProp context (.rField index expression) := by
  obtain ⟨hl1, hl2⟩ := h
  have hex :
      compileExpExactHOLW context (expToHOL expression) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) expression).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :=
    Prod.ext hl1.symm hl2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_5, compileExpExactHOLW.eq_5,
    expToHOL.eq_4, hex]
  cases hshape : (compileExpHOL (CompileExpContextExact.prodContext context) expression).2 with
  | one =>
      constructor <;>
        simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
  | comb fields =>
      have hcf := compileField_map_codecs index fields
        (compileExpHOL (CompileExpContextExact.prodContext context) expression).1
      simp only [shapeToHOL]
      exact hcf
  | named nm =>
      constructor <;>
        simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]

theorem compileExpBridge_load {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (shape : Shape)
    (expression : Exp (BitVec width))
    (h : compileExpBridgeProp context expression) :
    compileExpBridgeProp context (.load shape expression) := by
  obtain ⟨hl1, hl2⟩ := h
  have hex :
      compileExpExactHOLW context (expToHOL expression) =
        ((compileExpHOL (CompileExpContextExact.prodContext context) expression).1.map
            crepExpToHOL,
          shapeToHOL
            (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :=
    Prod.ext hl1.symm hl2.symm
  simp only [compileExpBridgeProp, compileExpHOL.eq_8, compileExpExactHOLW.eq_8,
    expToHOL.eq_7, hex, sizeOfShapeHOL_shapeToHOL]
  cases hcomp : compileExpHOL (CompileExpContextExact.prodContext context) expression with
  | mk l s =>
    cases l with
    | nil =>
        constructor <;>
          simp only [List.map_cons, List.map_nil, crepExpToHOL.eq_1, shapeToHOL]
    | cons a as =>
        simp only [List.map_cons]
        constructor
        · rw [loadShape_eq_loadShapeBytes_of_stride_eq (0 : BitVec width)
              (CrepBytesInWord.bytesInWord) (Shape.shapeSize shape) a rfl]
          exact loadShapeBytes_map_crepExpToHOL (0 : BitVec width) (Shape.shapeSize shape) a
        · trivial


/-! ### Assembly: the full `compile_exp` codec bridge

The top-level theorem is the `Flapjack.Exp.rec` assembly over all 17
constructors, using the per-constructor handlers above and the two list
handlers. -/

theorem compileExpBridge {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width)) :
    compileExpBridgeProp context expression :=
  Flapjack.Exp.rec
    (motive_1 := compileExpBridgeProp context)
    (motive_2 := compileExpListBridgeProp context)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (compileExpBridge_const context)
    (compileExpBridge_var context)
    (compileExpBridge_rStruct context)
    (compileExpBridge_rField context)
    (fun name fields _ => compileExpBridge_nStruct context name fields)
    (fun name value _ => compileExpBridge_nField context name value)
    (compileExpBridge_load context)
    (compileExpBridge_load32 context)
    (compileExpBridge_loadByte context)
    (compileExpBridge_op context)
    (compileExpBridge_panOp context)
    (compileExpBridge_cmp context)
    (compileExpBridge_shift context)
    (compileExpBridge_baseAddr context)
    (compileExpBridge_topAddr context)
    (compileExpBridge_bytesInWord context)
    (compileExpListBridgeProp_nil context)
    (compileExpListBridgeProp_cons context)
    True.intro
    (fun _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    expression

/-! ### Shape range in the exact-context expression path

An exact context stores only `ShapeHOL` values, and `expOfHOL` only decodes
`MlString` names. The compiler output-shape range fact is needed to decode the
paired expression result back to the production carrier without a premise. -/

private theorem compileField_shapeByteRanged {width : Nat} [NeZero width]
    (index : Nat) (shapes : List Shape)
    (hshapes : ∀ shape ∈ shapes, ShapeByteRanged shape)
    (expressions : List (CrepExp (BitVec width))) :
    ShapeByteRanged (compileField (α := BitVec width) index shapes expressions).2 := by
  induction shapes generalizing index expressions with
  | nil => simp [compileField, ShapeByteRanged]
  | cons shape shapes ih =>
      by_cases hzero : index = 0
      · simp [compileField, hzero, hshapes shape (by simp)]
      · have htail : ∀ field ∈ shapes, ShapeByteRanged field := by
          intro field hfield
          exact hshapes field (by simp [hfield])
        simpa [compileField, hzero] using
          ih (index - 1) htail (expressions.drop (Shape.shapeSize shape))

/-- Flapjack-specific compiler invariant (no HOL declaration has this bridge
    statement): when input syntax and local-variable shapes fit the byte-backed
    production carriers, `compile_exp` returns a byte-ranged shape. This is the
    representation premise needed to decode the exact result shape in
    `compileExpBridge_pair`; it does not claim a compiler-correctness result. -/
theorem compileExpHOL_shapeByteRanged {width : Nat} [NeZero width]
    (context : PanToCrepHOLContext (BitVec width))
    (hvars : ∀ name value, context.vars name = some value →
      ShapeByteRanged value.1) :
    (expression : Exp (BitVec width)) → ExpByteRanged expression →
      ShapeByteRanged (compileExpHOL context expression).2 :=
  Flapjack.Exp.rec
    (motive_1 := fun expression => ExpByteRanged expression →
      ShapeByteRanged (compileExpHOL context expression).2)
    (motive_2 := fun expressions => ListExpByteRanged expressions →
      ∀ result ∈ compileExpHOL.compileExpListHOL context expressions,
        ShapeByteRanged result.2)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (fun _value _ => by simp [compileExpHOL.eq_1, ShapeByteRanged])
    (fun kind name hname => by
      cases kind with
      | «local» =>
          cases hlookup : context.vars name with
          | none => simp [compileExpHOL.eq_2, FLOOKUP, hlookup, ShapeByteRanged]
          | some value =>
              simpa [compileExpHOL.eq_2, FLOOKUP, hlookup] using hvars name value hlookup
      | global => simp [compileExpHOL.eq_3, ShapeByteRanged])
    (fun expressions ih hexpressions => by
      simp only [compileExpHOL.eq_4, ShapeByteRanged]
      intro shape hshape
      obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hshape
      exact ih hexpressions result hresult)
    (fun index expression ih hexpression => by
      cases hshape : (compileExpHOL context expression).2 with
      | one => simp [compileExpHOL.eq_5, hshape, ShapeByteRanged]
      | named name => simp [compileExpHOL.eq_5, hshape, ShapeByteRanged]
      | comb shapes =>
          have hfields : ∀ shape ∈ shapes, ShapeByteRanged shape := by
            simpa [ShapeByteRanged, hshape] using ih hexpression
          simpa [compileExpHOL.eq_5, hshape] using
            compileField_shapeByteRanged index shapes hfields
              (compileExpHOL context expression).1)
    (fun _name _fields _ihs _ => by simp [compileExpHOL.eq_6, ShapeByteRanged])
    (fun _name _value _ih _ => by simp [compileExpHOL.eq_7, ShapeByteRanged])
    (fun shape _address _ih hload => by
      rcases hload with ⟨hshape, _⟩
      cases hcompiled : compileExpHOL context _address with
      | mk values resultShape =>
          cases values <;> simp [compileExpHOL.eq_8, hcompiled, hshape,
            ShapeByteRanged])
    (fun _address _ih _ => by
      cases hcompiled : compileExpHOL context _address with
      | mk values shape => cases values <;> cases shape <;>
          simp [compileExpHOL.eq_9, hcompiled, ShapeByteRanged])
    (fun _address _ih _ => by
      cases hcompiled : compileExpHOL context _address with
      | mk values shape => cases values <;> cases shape <;>
          simp [compileExpHOL.eq_10, hcompiled, ShapeByteRanged])
    (fun _operator expressions _ih _ => by
      cases hheads : cexpHeads
          ((compileExpHOL.compileExpListHOL context expressions).map Prod.fst) <;>
        simp [compileExpHOL.eq_11, hheads, ShapeByteRanged])
    (fun _operator expressions _ih _ => by
      cases hheads : cexpHeads
          ((compileExpHOL.compileExpListHOL context expressions).map Prod.fst) <;>
        simp [compileExpHOL.eq_12, hheads, ShapeByteRanged])
    (fun _operator left right _ihl _ihr _ => by
      cases hleft : compileExpHOL context left with
      | mk leftValues leftShape =>
        cases hright : compileExpHOL context right with
        | mk rightValues rightShape =>
          cases leftValues <;> cases rightValues <;>
            simp [compileExpHOL.eq_13, hleft, hright, ShapeByteRanged])
    (fun _operator left right _ihl _ihr _ => by
      cases hleft : compileExpHOL context left with
      | mk leftValues leftShape =>
        cases hright : compileExpHOL context right with
        | mk rightValues rightShape =>
          cases leftValues <;> cases rightValues <;>
            simp [compileExpHOL.eq_14, hleft, hright, ShapeByteRanged])
    (by simp [compileExpHOL.eq_15, ShapeByteRanged])
    (by simp [compileExpHOL.eq_16, ShapeByteRanged])
    (by simp [compileExpHOL.eq_17, ShapeByteRanged])
    (by simp [compileExpHOL.compileExpListHOL])
    (fun head tail ihHead ihTail hlist => by
      intro result hresult
      simp only [compileExpHOL.compileExpListHOL.eq_2,
        List.mem_cons] at hresult
      rcases hresult with hhead | htail
      · simpa [hhead] using ihHead hlist.1
      · exact ihTail hlist.2 _ htail)
    True.intro
    (fun _head _tail _ih1 _ih2 => True.intro)
    (fun _fst _snd _ih => True.intro)

private theorem compileExpListHOL_eq_of_pointwise {width : Nat} [NeZero width]
    (left right : PanToCrepHOLContext (BitVec width))
    (expressions : List (Exp (BitVec width)))
    (hpoint : ∀ expression ∈ expressions,
      compileExpHOL left expression = compileExpHOL right expression) :
    compileExpHOL.compileExpListHOL left expressions =
      compileExpHOL.compileExpListHOL right expressions := by
  induction expressions with
  | nil => simp [compileExpHOL.compileExpListHOL]
  | cons head tail ih =>
      simp only [compileExpHOL.compileExpListHOL.eq_2]
      rw [hpoint head (by simp)]
      congr 1
      apply ih
      intro expression hmem
      exact hpoint expression (by simp [hmem])

/-- Expression-compiler congruence for contexts whose variable maps agree on
    byte-ranged names. `compileExpHOL` does not inspect the function or
    exception maps. This is the production-side congruence needed to carry the
    exact-to-production context relation through recursive Dec/DecCall bodies;
    arbitrary String keys remain outside its premise. -/
theorem compileExpHOL_congr_of_ranged_vars {width : Nat} [NeZero width]
    (left right : PanToCrepHOLContext (BitVec width))
    (hvars : ∀ name, NameRanged name → left.vars name = right.vars name) :
    (expression : Exp (BitVec width)) → ExpByteRanged expression →
      compileExpHOL left expression = compileExpHOL right expression :=
  Flapjack.Exp.rec
    (motive_1 := fun expression => ExpByteRanged expression →
      compileExpHOL left expression = compileExpHOL right expression)
    (motive_2 := fun expressions => ListExpByteRanged expressions →
      ∀ expression ∈ expressions,
        compileExpHOL left expression = compileExpHOL right expression)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (fun _value _ => by simp [compileExpHOL.eq_1])
    (fun kind name hname => by
      cases kind with
      | «local» =>
          simp only [ExpByteRanged] at hname
          simp [compileExpHOL.eq_2, FLOOKUP, hvars name hname]
      | global => simp [compileExpHOL.eq_3])
    (fun expressions ih hexpressions => by
      have hpoint : ∀ expression ∈ expressions,
          compileExpHOL left expression = compileExpHOL right expression :=
        ih hexpressions
      have hcompiled := compileExpListHOL_eq_of_pointwise left right expressions hpoint
      simp only [compileExpHOL.eq_4, hcompiled])
    (fun _index expression ih hexpression => by
      simp [compileExpHOL.eq_5, ih hexpression])
    (fun _name _fields _ihs _ => by simp [compileExpHOL.eq_6])
    (fun _name _expression _ih _ => by
      simp [compileExpHOL.eq_7])
    (fun _shape expression ih hexpression => by
      simp [compileExpHOL.eq_8, ih hexpression.2])
    (fun expression ih hexpression => by
      simp [compileExpHOL.eq_9, ih hexpression])
    (fun expression ih hexpression => by
      simp [compileExpHOL.eq_10, ih hexpression])
    (fun _operator expressions ih hexpressions => by
      have hpoint : ∀ expression ∈ expressions,
          compileExpHOL left expression = compileExpHOL right expression :=
        ih hexpressions
      have hcompiled := compileExpListHOL_eq_of_pointwise left right expressions hpoint
      simp [compileExpHOL.eq_11, hcompiled])
    (fun _operator expressions ih hexpressions => by
      have hpoint : ∀ expression ∈ expressions,
          compileExpHOL left expression = compileExpHOL right expression :=
        ih hexpressions
      have hcompiled := compileExpListHOL_eq_of_pointwise left right expressions hpoint
      simp [compileExpHOL.eq_12, hcompiled])
    (fun _operator leftExp rightExp ihLeft ihRight hparent => by
      simp [compileExpHOL.eq_13, ihLeft hparent.1, ihRight hparent.2])
    (fun _operator leftExp rightExp ihLeft ihRight hparent => by
      simp [compileExpHOL.eq_14, ihLeft hparent.1, ihRight hparent.2])
    (by simp [compileExpHOL.eq_15])
    (by simp [compileExpHOL.eq_16])
    (by simp [compileExpHOL.eq_17])
    (by simp)
    (fun head tail ihHead ihTail hlist => by
      intro expression hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | htail
      · subst expression
        exact ihHead hlist.1
      · exact ihTail hlist.2 _ htail)
    True.intro
    (fun _head _tail _ih1 _ih2 => True.intro)
    (fun _fst _snd _ih => True.intro)

/-! ### Codec-direction corollaries

`compileExpBridge` is stated in the `crepExpToHOL` direction. Downstream
executable-path routing often wants the exact result mapped back to the
production carrier, which is the `crepExpOfHOL` direction below. The expression
list direction is unconditional (`crepExpOfHOL` is a total left inverse of
`crepExpToHOL`); the shape direction needs `ShapeByteRanged`, because
`shapeOfHOL` only inverts `shapeToHOL` on byte-ranged shapes. -/

theorem compileExpBridge_codecImage {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width)) :
    (compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL
      = (compileExpHOL (CompileExpContextExact.prodContext context) expression).1 := by
  have h := (compileExpBridge context expression).1
  have hcomp : (crepExpOfHOL (width := width) ∘ crepExpToHOL (width := width)) = id :=
    funext (fun x => crepExpOfHOL_crepExpToHOL (width := width) x)
  rw [← h, List.map_map, hcomp, List.map_id]

theorem compileExpBridge_shapeOfHOL {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width))
    (hbyte : ShapeByteRanged
      (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :
    shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2
      = (compileExpHOL (CompileExpContextExact.prodContext context) expression).2 := by
  rw [← (compileExpBridge context expression).2]
  exact shapeOfHOL_shapeToHOL _ hbyte

theorem compileExpBridge_pair {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : Exp (BitVec width))
    (hbyte : ShapeByteRanged
      (compileExpHOL (CompileExpContextExact.prodContext context) expression).2) :
    ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2)
      = compileExpHOL (CompileExpContextExact.prodContext context) expression :=
  Prod.ext (compileExpBridge_codecImage context expression)
    (compileExpBridge_shapeOfHOL context expression hbyte)

private theorem compileExpHOL_exact_shapeByteRanged {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : ExpHOL width) :
    ShapeByteRanged
      (compileExpHOL (CompileExpContextExact.prodContext context)
        (expOfHOL expression)).2 := by
  apply compileExpHOL_shapeByteRanged
  · intro name value hlookup
    change Option.map (fun entry => (shapeOfHOL entry.1, entry.2))
      (context.vars.lookup (ofString name)) = some value at hlookup
    cases hmap : context.vars.lookup (ofString name) with
    | none => simp [hmap] at hlookup
    | some entry =>
        simp only [hmap, Option.map_some, Option.some.injEq] at hlookup
        cases hlookup
        exact shapeOfHOL_byteRanged entry.1
  · exact expOfHOL_byteRanged expression

/-- The exact expression compiler's decoded output is unconditionally the
    production compiler result for every exact context and HOL expression.
    This is Flapjack bridge infrastructure (there is no separate HOL theorem
    with this paired representation statement). -/
theorem compileExpExactHOLW_prodCodec {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (expression : ExpHOL width) :
    ((compileExpExactHOLW context expression).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context expression).2)
      = compileExpHOL (CompileExpContextExact.prodContext context)
          (expOfHOL expression) := by
  simpa only [expToHOL_expOfHOL] using
    compileExpBridge_pair context (expOfHOL expression)
      (compileExpHOL_exact_shapeByteRanged context expression)

/-- The exact expression codec remains valid when the production context is
    related to the exact context only on source-reachable byte-ranged variable
    keys. This is the context-general form needed by the recursive program
    bridge after Dec/DecCall updates. -/
theorem compileExpExactHOLW_prodCodec_of_ranged_vars {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (production : PanToCrepHOLContext (BitVec width))
    (hvars : ∀ name, NameRanged name →
      context.toProduction.vars name = production.vars name)
    (expression : ExpHOL width) :
    ((compileExpExactHOLW context expression).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context expression).2)
      = compileExpHOL production (expOfHOL expression) := by
  have hcodec := compileExpExactHOLW_prodCodec context expression
  calc
    _ = compileExpHOL context.toProduction (expOfHOL expression) := by
      simpa [CompileExpContextExact.prodContext] using hcodec
    _ = compileExpHOL production (expOfHOL expression) :=
      compileExpHOL_congr_of_ranged_vars context.toProduction production hvars
        (expOfHOL expression) (expOfHOL_byteRanged expression)

end Flapjack
