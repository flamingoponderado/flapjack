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

theorem expOfHOL_byteRanged {width : Nat} [NeZero width] :
    (expression : ExpHOL width) → ExpByteRanged (expOfHOL expression) := by
  intro expression
  fun_induction expOfHOL expression with
  | case2 _ name => exact stringOfBytes_byteRanged name
  | case6 name _ ih => exact ⟨stringOfBytes_byteRanged name, ih⟩
  | case5 name fields ih =>
      refine ⟨stringOfBytes_byteRanged name, ?_⟩
      rw [listFieldByteRanged_iff_forall_mem]
      intro field hfield
      obtain ⟨⟨fieldName, value⟩, hsource, rfl⟩ := List.mem_map.mp hfield
      exact ⟨stringOfBytes_byteRanged fieldName, ih (fieldName, value) hsource⟩
  | _ =>
      simp_all [ExpByteRanged, listExpByteRanged_iff_forall_mem, shapeOfHOL_byteRanged]

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

end Flapjack
