module

public import Flapjack.Pancake.PanStructs
public import Flapjack.Pancake.PanLang.Decl
public import Flapjack.Pancake.PanLang.Prog
public import Flapjack.Pancake.PanStructs.CompileShapeExact
public import Flapjack.Pancake.PanStructs.OldExpShapeExact

@[expose] public section

/-!
The pass rewrites every shape in a declaration through
`structCompileShape`, so proving `DeclByteRanged` survives it needs
byte-rangedness of the struct shapes, the compiled expressions, and the
compiled programs, carried by the struct context invariant `CtxBR`.
Nothing here is a HOL port; the definitions already live in
`PanStructs.lean`, and these lemmas are Flapjack-specific infrastructure
for the executed parser-to-Crep boundary.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Byte-rangedness of the production struct context used by the struct pass. -/
def CtxBR (c : StructContext) : Prop :=
  ∀ p ∈ c, NameRanged p.1 ∧ ListParamByteRanged p.2.fields

theorem lookupInfoWithRest_exists_mem [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) :
    ∃ k, (k, info) ∈ context := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hc : entry.1 == name
      · simp only [lookupInfoWithRest, hc] at h
        injection h with hp
        injection hp with h1 _
        exact ⟨entry.1, by simp only [List.mem_cons]; left; cases entry; simp_all⟩
      · simp only [lookupInfoWithRest, hc] at h
        obtain ⟨k, hk⟩ := ih h
        exact ⟨k, by simp [hk]⟩

theorem lookupInfoWithRest_ctxBR [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) (hc : CtxBR context) :
    CtxBR suffix := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hmatch : entry.1 == name
      · simp only [lookupInfoWithRest, hmatch] at h
        injection h with hp
        injection hp with _ h2
        subst h2
        exact fun p hp => hc p (by simp [hp])
      · simp only [lookupInfoWithRest, hmatch] at h
        exact ih h (fun p hp => hc p (by simp [hp]))

theorem structCompileShapeWF_byteRanged (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    ShapeByteRanged (structCompileShapeWF context shape) := by
  refine (structCompileShapeWF.induct
    (motive1 := fun context shapes => CtxBR context → (∀ s ∈ shapes, ShapeByteRanged s) →
        ∀ s ∈ structCompileShapeWF.structCompileShapesWF context shapes, ShapeByteRanged s)
    (motive2 := fun context shape => CtxBR context → ShapeByteRanged shape →
        ShapeByteRanged (structCompileShapeWF context shape)) ?_ ?_ ?_ ?_ ?_ ?_) context shape hc hs
  · intro _context _ _ s hs
    simp [structCompileShapeWF.structCompileShapesWF] at hs
  · intro context shape shapes ihshape ihshapes hctx hcons s hmem
    simp only [structCompileShapeWF.structCompileShapesWF] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact ihshape hctx (hcons shape (by simp))
    · exact ihshapes hctx (fun t ht => hcons t (by simp [ht])) s hmem'
  · intro _context _ _
    simp [structCompileShapeWF, ShapeByteRanged]
  · intro context shapes ihshapes hctx hcomb
    rw [structCompileShapeWF]
    simp only [ShapeByteRanged] at hcomb ⊢
    exact ihshapes hctx hcomb
  · intro context name info suffix hlookup ihfields hctx _hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info' suffix' heq
      rw [hlookup] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [ShapeByteRanged]
      refine ihfields (lookupInfoWithRest_ctxBR hlookup hctx) ?_
      intro s hsinfo
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hsinfo
      obtain ⟨k, hk⟩ := lookupInfoWithRest_exists_mem hlookup
      exact ((hctx (k, info) hk).2 p hp).2
    · rename_i heq
      rw [hlookup] at heq
      simp at heq
  · intro context name hlookup _hctx _hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info' suffix' heq
      rw [hlookup] at heq
      simp at heq
    · simp [ShapeByteRanged]

/-- Project the production structure context onto the exact fields-only carrier
consumed by HOL `compile_shape`. -/
def structContextToCompileShapeExact (context : StructContext) :
    List (MlS × List (MlS × ShapeHOL)) :=
  context.map fun entry =>
    (ofString entry.1, entry.2.fields.map fun field => (ofString field.1, shapeToHOL field.2))

/-- Flapjack codec infrastructure, with no HOL original: encode all three
production context fields without cached StructInfo sizes. -/
def structPassContextToExact (context : StructPassContext) :
    Flapjack.Pancake.PanStructs.CompileShapeExact.ContextExact :=
  { structs := structContextToCompileShapeExact context.structs
    locals := context.locals.map fun p => (ofString p.1, shapeToHOL p.2)
    globals := context.globals.map fun p => (ofString p.1, shapeToHOL p.2) }

private theorem ofString_injective_of_ranged_local {a b : String}
    (ha : NameRanged a) (hb : NameRanged b) (h : ofString a = ofString b) : a = b := by
  have h' := congrArg toStringOfBytes h
  rwa [toStringOfBytes_ofString_of_bytes a ha,
    toStringOfBytes_ofString_of_bytes b hb] at h'

/-- The exact HOL first-match search and production `lookupInfoWithRest` select
the same entry and suffix when identifiers are byte-ranged. -/
theorem structContextToCompileShapeExact_dropWhile
    (name : String) (context : StructContext) (hc : CtxBR context)
    (hn : NameRanged name) :
    (structContextToCompileShapeExact context).dropWhile
        (fun entry => ! decide (entry.1 = ofString name)) =
      match lookupInfoWithRest name context with
      | none => []
      | some (info, suffix) =>
          (ofString name,
            info.fields.map fun field => (ofString field.1, shapeToHOL field.2)) ::
              structContextToCompileShapeExact suffix := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, info⟩ := entry
      have hcand : NameRanged candidate := (hc (candidate, info) (by simp)).1
      have hrest : CtxBR rest := fun p hp => hc p (by simp [hp])
      by_cases hmatch : candidate == name
      · have heq : candidate = name := beq_iff_eq.mp hmatch
        subst candidate
        simp [structContextToCompileShapeExact, lookupInfoWithRest]
      · have hnot : ofString candidate ≠ ofString name := by
          intro heq
          apply hmatch
          apply beq_iff_eq.mpr
          exact ofString_injective_of_ranged_local hcand hn heq
        have hdrop : decide (ofString candidate = ofString name) = false :=
          by simp [hnot]
        simp only [structContextToCompileShapeExact, List.map_cons,
          List.dropWhile_cons, hdrop, Bool.not_false, lookupInfoWithRest, hmatch]
        exact ih hrest

/-- On parser-ranged identifiers and shapes, production `compile_shape`
agrees with the reviewed exact HOL `compile_shape` after the checked carrier
conversion. This is an untagged bridge theorem; it does not change which
definition the executable pass calls. -/
theorem structCompileShapeWF_eq_compileShapeExact
    (context : StructContext) (shape : Shape) (hc : CtxBR context)
    (hs : ShapeByteRanged shape) :
    structCompileShapeWF context shape =
      shapeOfHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact
        (structContextToCompileShapeExact context) (shapeToHOL shape)) := by
  refine (structCompileShapeWF.induct
    (motive1 := fun context shapes => CtxBR context →
      (∀ s ∈ shapes, ShapeByteRanged s) →
        structCompileShapeWF.structCompileShapesWF context shapes =
          (Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapesExact
            (structContextToCompileShapeExact context) (shapes.map shapeToHOL)).map shapeOfHOL)
    (motive2 := fun context shape => CtxBR context → ShapeByteRanged shape →
      structCompileShapeWF context shape =
        shapeOfHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact
          (structContextToCompileShapeExact context) (shapeToHOL shape)))
    ?_ ?_ ?_ ?_ ?_ ?_) context shape hc hs
  · intro context hc _hs
    simp [structCompileShapeWF.structCompileShapesWF,
      Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapesExact]
  · intro context shape shapes ihshape ihshapes hc hshapes
    simp only [structCompileShapeWF.structCompileShapesWF,
      Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapesExact,
      List.map_cons]
    rw [ihshape hc (hshapes shape (by simp))]
    rw [ihshapes hc (fun s hmem => hshapes s (by simp [hmem]))]
  · intro _context hc hs
    simp [structCompileShapeWF,
      Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact,
      shapeOfHOL, shapeToHOL]
  · intro context shapes ih hc hshapes
    simp only [structCompileShapeWF,
      Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact,
      shapeOfHOL, shapeToHOL]
    have hchildren : ∀ s ∈ shapes, ShapeByteRanged s := by
      simpa only [ShapeByteRanged] using hshapes
    exact congrArg Shape.comb (ih hc hchildren)
  · intro context name info suffix hlookup ih hc hnamed
    have hname : NameRanged name := by simpa only [ShapeByteRanged] using hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info' suffix' heq
      rw [hlookup] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [shapeToHOL,
        Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact]
      rw [structContextToCompileShapeExact_dropWhile name context hc hname]
      rw [hlookup]
      simp only [shapeOfHOL]
      have hfields : ∀ s ∈ info.fields.map Prod.snd, ShapeByteRanged s := by
        intro s hs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        obtain ⟨k, hk⟩ := lookupInfoWithRest_exists_mem hlookup
        exact ((hc (k, info) hk).2 p hp).2
      have hctxsuffix : CtxBR suffix := lookupInfoWithRest_ctxBR hlookup hc
      simpa [Function.comp_def] using
        congrArg Shape.comb (ih hctxsuffix hfields)
    · rename_i heq
      rw [hlookup] at heq
      simp at heq
  · intro context name hlookup hc hnamed
    have hname : NameRanged name := by simpa only [ShapeByteRanged] using hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info suffix heq
      rw [hlookup] at heq
      simp at heq
    · have hdrop := structContextToCompileShapeExact_dropWhile name context hc hname
      have hdropNone :
          (structContextToCompileShapeExact context).dropWhile
            (fun entry => ! decide (entry.1 = ofString name)) = [] := by
        rw [hdrop, hlookup]
      simp only [shapeToHOL,
        Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact]
      rw [hdropNone]
      simp [shapeOfHOL]

/-- Exact HOL-shape callback for the parser-proved struct pass. -/
def structCompileShapeExactProduction (context : StructContext) (shape : Shape) : Shape :=
  shapeOfHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact
    (structContextToCompileShapeExact context) (shapeToHOL shape))

theorem structCompileShape_byteRanged (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    ShapeByteRanged (structCompileShape context shape) :=
  structCompileShapeWF_byteRanged context shape hc hs

private theorem listExpByteRanged_iff {width : Nat} (l : List (Exp (BitVec width))) :
    ListExpByteRanged l ↔ ∀ e ∈ l, ExpByteRanged e := by
  induction l with
  | nil => simp [ListExpByteRanged]
  | cons e es ih =>
    constructor
    · intro h e' he'
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact h.1
      · exact ih.mp h.2 e' he'
    · intro h
      exact ⟨h e (by simp), ih.mpr (fun x hx => h x (by simp [hx]))⟩

private theorem listFieldByteRanged_iff {width : Nat} (l : List (String × Exp (BitVec width))) :
    ListFieldByteRanged l ↔
      ∀ p ∈ l, (∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2 := by
  induction l with
  | nil => simp [ListFieldByteRanged]
  | cons p ps ih =>
    constructor
    · intro h q hq
      rw [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨h.1, h.2.1⟩
      · exact ih.mp h.2.2 q hq
    · intro h
      exact ⟨(h p (by simp)).1, (h p (by simp)).2, ih.mpr (fun q hq => h q (by simp [hq]))⟩

private theorem lookupInfo_value_byteRanged [BEq String] {key : String}
    {entries : List (String × Exp (BitVec width))} {value : Exp (BitVec width)}
    (h : lookupInfo key entries = some value)
    (hall : ∀ p ∈ entries, ExpByteRanged p.2) : ExpByteRanged value := by
  induction entries with
  | nil => simp [lookupInfo] at h
  | cons entry rest ih =>
    obtain ⟨candidate, v⟩ := entry
    by_cases hc : candidate == key
    · simp only [lookupInfo, hc] at h
      injection h with h
      subst h
      exact hall (candidate, v) (by simp)
    · simp only [lookupInfo, hc] at h
      exact ih h (fun p hp => hall p (by simp [hp]))

theorem structSelectFields_byteRanged [BEq String]
    (fields : List (FieldName × Shape)) (compiled : List (String × Exp (BitVec width)))
    (h : ∀ p ∈ compiled, ExpByteRanged p.2) :
    ∀ e ∈ structSelectFields fields compiled, ExpByteRanged e := by
  induction fields with
  | nil => intro e he; simp [structSelectFields] at he
  | cons f fs ih =>
    obtain ⟨field, shape⟩ := f
    intro e he
    simp only [structSelectFields] at he
    split at he
    · rename_i expression hlookup
      rw [List.mem_cons] at he
      rcases he with rfl | he'
      · exact lookupInfo_value_byteRanged hlookup h
      · exact ih e he'
    · exact ih e he

theorem structCompileExp_byteRanged {width : Nat} [BEq String] (context : StructPassContext)
    (hc : CtxBR context.structs) :
    ∀ e : Exp (BitVec width), ExpByteRanged e → ExpByteRanged (structCompileExp context e) := by
  have hgeneral : ∀ (e : Exp (BitVec width))
      (compileShape : StructContext → Shape → Shape)
      (oldExpShape : StructPassContext → Exp (BitVec width) → Shape),
      compileShape = structCompileShape → ExpByteRanged e →
        ExpByteRanged (structCompileExp context e compileShape oldExpShape) := by
    exact (structCompileExp.induct (α := BitVec width) context
    (motive1 := fun l compileShape oldExpShape => compileShape = structCompileShape →
        (∀ e ∈ l, ExpByteRanged e) →
          ∀ e ∈ structCompileExp.structCompileExps context l compileShape oldExpShape,
            ExpByteRanged e)
    (motive2 := fun e compileShape oldExpShape => compileShape = structCompileShape →
        ExpByteRanged e → ExpByteRanged (structCompileExp context e compileShape oldExpShape))
    (motive3 := fun l compileShape oldExpShape => compileShape = structCompileShape →
        (∀ p ∈ l, ExpByteRanged p.2) →
          ∀ p ∈ structCompileExp.structCompileFields context l compileShape oldExpShape,
            ExpByteRanged p.2)
    (by
      intro compileShape oldExpShape hcb hall e he
      simp [structCompileExp.structCompileExps] at he)
    (by
    intro e es compileShape oldExpShape ihe ihes hcb hall x hx
    simp only [structCompileExp.structCompileExps] at hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ihe hcb (hall e (by simp))
    · exact ihes hcb (fun y hy => hall y (by simp [hy])) x hx')
    (by
      intro fields compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro index value compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      simp only [ExpByteRanged] at hv ⊢
      exact ih hcb hv)
    (by
      intro name fields compileShape oldExpShape info hlookup ihfields hcb hv
      rw [structCompileExp]
      simp only [hlookup]
      exact (listExpByteRanged_iff _).mpr
        (structSelectFields_byteRanged info.fields _
          (ihfields hcb (fun p hp => ((listFieldByteRanged_iff fields).mp hv.2 p hp).2))))
    (by
      intro name fields compileShape oldExpShape hlookup ihfields hcb _hv
      rw [structCompileExp]
      simp only [hlookup]
      simp [ExpByteRanged, ListExpByteRanged])
    (by
      intro field value compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      simp only [ExpByteRanged] at hv ⊢
      exact ih hcb hv.2)
    (by
      intro shape address compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      subst compileShape
      exact ⟨structCompileShape_byteRanged context.structs shape hc hv.1, ih rfl hv.2⟩)
    (by
      intro address compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      exact ih hcb hv)
    (by
      intro address compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      exact ih hcb hv)
    (by
      intro operator arguments compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator arguments compileShape oldExpShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator left right compileShape oldExpShape ihl ihr hcb hv
      rw [structCompileExp]
      exact ⟨ihl hcb hv.1, ihr hcb hv.2⟩)
    (by
      intro operator left right compileShape oldExpShape ihl ihr hcb hv
      rw [structCompileExp]
      exact ⟨ihl hcb hv.1, ihr hcb hv.2⟩)
    (by
      intro compileShape oldExpShape expression h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hcb hv
      subst compileShape
      cases expression with
      | const v => simp [structCompileExp, ExpByteRanged]
      | var k name => simpa [structCompileExp] using hv
      | baseAddr => simp [structCompileExp, ExpByteRanged]
      | topAddr => simp [structCompileExp, ExpByteRanged]
      | bytesInWord => simp [structCompileExp, ExpByteRanged]
      | rStruct fs => exact (h1 fs rfl).elim
      | rField i v => exact (h2 i v rfl).elim
      | nStruct nm fs => exact (h3 nm fs rfl).elim
      | nField f v => exact (h4 f v rfl).elim
      | load sh a => exact (h5 sh a rfl).elim
      | load32 a => exact (h6 a rfl).elim
      | loadByte a => exact (h7 a rfl).elim
      | op o args => exact (h8 o args rfl).elim
      | panOp o args => exact (h9 o args rfl).elim
      | cmp o l r => exact (h10 o l r rfl).elim
      | shift o l r => exact (h11 o l r rfl).elim)
    (by
      intro compileShape oldExpShape hcb _ p hp
      simp [structCompileExp.structCompileFields] at hp)
    (by
      intro field expression fields compileShape oldExpShape ihe ih hcb hall p hp
      simp only [structCompileExp.structCompileFields] at hp
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact ihe hcb (hall (field, expression) (by simp))
      · exact ih hcb (fun q hq => hall q (by simp [hq])) p hp'))
  intro e he
  exact hgeneral e structCompileShape structOldExpShape rfl he

private theorem structCompileExp_eq_of_shape_eq {width : Nat} [BEq String]
    (context : StructPassContext) (compileShape : StructContext → Shape → Shape) :
    (∀ shape, ShapeByteRanged shape →
      compileShape context.structs shape = structCompileShape context.structs shape) →
    ∀ expression : Exp (BitVec width), ExpByteRanged expression →
      structCompileExp context expression compileShape = structCompileExp context expression := by
  have hgeneral : ∀ (expression : Exp (BitVec width))
      (compileShape : StructContext → Shape → Shape)
      (oldExpShape : StructPassContext → Exp (BitVec width) → Shape),
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      ExpByteRanged expression →
        structCompileExp context expression compileShape oldExpShape =
          structCompileExp context expression structCompileShape oldExpShape := by
    exact (structCompileExp.induct (α := BitVec width) context
    (motive1 := fun expressions compileShape oldExpShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        structCompileExp.structCompileExps context expressions compileShape oldExpShape =
          structCompileExp.structCompileExps context expressions structCompileShape oldExpShape)
    (motive2 := fun expression compileShape oldExpShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      ExpByteRanged expression →
        structCompileExp context expression compileShape oldExpShape =
          structCompileExp context expression structCompileShape oldExpShape)
    (motive3 := fun fields compileShape oldExpShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      (∀ field ∈ fields, ExpByteRanged field.2) →
        structCompileExp.structCompileFields context fields compileShape oldExpShape =
          structCompileExp.structCompileFields context fields structCompileShape oldExpShape)
    (by
      intro compileShape oldExpShape hshape hall
      simp [structCompileExp.structCompileExps])
    (by
      intro expression expressions compileShape oldExpShape ihe ih hshape hall
      simp only [structCompileExp.structCompileExps]
      rw [ihe hshape (hall expression (by simp))]
      rw [ih hshape (fun item hitem => hall item (by simp [hitem]))])
    (by
      intro fields compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.rStruct (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro index value compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.rField index) (ih hshape hv))
    (by
      intro name fields compileShape oldExpShape info hlookup ih hshape hv
      simp only [structCompileExp, hlookup]
      rw [ih hshape (fun field hfield =>
        ((listFieldByteRanged_iff fields).mp hv.2 field hfield).2)])
    (by
      intro name fields compileShape oldExpShape hlookup ih hshape _hv
      simp only [structCompileExp, hlookup])
    (by
      intro field value compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.rField (match oldExpShape context value with
        | .named name =>
            match lookupInfo name context.structs with
            | some info => (structFindFieldIndex field info.fields).getD 0
            | none => 0
        | _ => 0)) (ih hshape hv.2))
    (by
      intro shape address compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      rw [hshape shape hv.1, ih hshape hv.2])
    (by
      intro address compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.load32 (ih hshape hv))
    (by
      intro address compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.loadByte (ih hshape hv))
    (by
      intro operator arguments compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.op operator) (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator arguments compileShape oldExpShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.panOp operator) (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator left right compileShape oldExpShape ihl ihr hshape hv
      simp only [structCompileExp]
      simp only [Exp.cmp.injEq]
      exact ⟨trivial, ihl hshape hv.1, ihr hshape hv.2⟩)
    (by
      intro operator left right compileShape oldExpShape ihl ihr hshape hv
      simp only [structCompileExp]
      simp only [Exp.shift.injEq]
      exact ⟨trivial, ihl hshape hv.1, ihr hshape hv.2⟩)
    (by
      intro compileShape oldExpShape expression h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hshape hv
      cases expression with
      | const value => simp [structCompileExp]
      | var kind name => simp [structCompileExp]
      | baseAddr => simp [structCompileExp]
      | topAddr => simp [structCompileExp]
      | bytesInWord => simp [structCompileExp]
      | rStruct fields => exact (h1 fields rfl).elim
      | rField index value => exact (h2 index value rfl).elim
      | nStruct name fields => exact (h3 name fields rfl).elim
      | nField field value => exact (h4 field value rfl).elim
      | load shape address => exact (h5 shape address rfl).elim
      | load32 address => exact (h6 address rfl).elim
      | loadByte address => exact (h7 address rfl).elim
      | op operator arguments => exact (h8 operator arguments rfl).elim
      | panOp operator arguments => exact (h9 operator arguments rfl).elim
      | cmp operator left right => exact (h10 operator left right rfl).elim
      | shift operator left right => exact (h11 operator left right rfl).elim)
    (by
      intro compileShape oldExpShape hshape hall
      simp [structCompileExp.structCompileFields])
    (by
      intro field expression fields compileShape oldExpShape ihe ih hshape hall
      simp only [structCompileExp.structCompileFields]
      simp only [ihe hshape (hall (field, expression) (by simp)),
        ih hshape (fun pair hpair => hall pair (by simp [hpair]))]))
  intro hshape expression he
  exact hgeneral expression compileShape structOldExpShape hshape he

theorem structCompileShapeExactProduction_eq_legacy
    (context : StructContext) (shape : Shape) (hc : CtxBR context)
    (hs : ShapeByteRanged shape) :
    structCompileShapeExactProduction context shape = structCompileShape context shape := by
  unfold structCompileShapeExactProduction structCompileShape
  exact (structCompileShapeWF_eq_compileShapeExact context shape hc hs).symm

private theorem structCompileExp_exact_eq_legacy {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ expression : Exp (BitVec width), ExpByteRanged expression →
      structCompileExp context expression structCompileShapeExactProduction =
        structCompileExp context expression := by
  apply structCompileExp_eq_of_shape_eq context structCompileShapeExactProduction
  · intro shape hshape
    exact structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape

private theorem structCompileExps_eq_of_shape_eq {width : Nat} [BEq String]
    (context : StructPassContext) (compileShape : StructContext → Shape → Shape)
    (hshape : ∀ shape, ShapeByteRanged shape →
      compileShape context.structs shape = structCompileShape context.structs shape) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        structCompileExp.structCompileExps context expressions compileShape =
          structCompileExp.structCompileExps context expressions
  | [], _ => by simp [structCompileExp.structCompileExps]
  | expression :: expressions, hall => by
      simp only [structCompileExp.structCompileExps]
      congr 1
      · exact structCompileExp_eq_of_shape_eq context compileShape hshape expression
          (hall expression (by simp))
      · exact structCompileExps_eq_of_shape_eq context compileShape hshape expressions
          (fun item hitem => hall item (by simp [hitem]))

private theorem structCompileExps_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        ∀ expression ∈ structCompileExp.structCompileExps context expressions,
          ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => simp [structCompileExp.structCompileExps]
  | cons expression rest ih =>
      intro hall compiled hmem
      simp only [structCompileExp.structCompileExps] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact structCompileExp_byteRanged context hc expression (hall expression (by simp))
      · exact ih (fun e he => hall e (by simp [he])) compiled htail

private theorem structCompileProgExps_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        ∀ expression ∈ structCompileProg.structCompileExps context expressions,
          ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => simp [structCompileProg.structCompileExps]
  | cons expression rest ih =>
      intro hall compiled hmem
      simp only [structCompileProg.structCompileExps] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact structCompileExp_byteRanged context hc expression (hall expression (by simp))
      · exact ih (fun e he => hall e (by simp [he])) compiled htail

theorem structCompileProg_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      ProgByteRanged (structCompileProg context program)
  | .skip, _ => by simp [ProgByteRanged, structCompileProg]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, hv, hb⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileShape_byteRanged context.structs shape hc hs,
        structCompileExp_byteRanged context hc value hv,
        structCompileProg_byteRanged { context with locals := (name, shape) :: context.locals } hc body hb⟩
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc value h.2⟩
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileProgExps_byteRanged context hc arguments h.2⟩
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileProg_byteRanged context hc first h.1,
        structCompileProg_byteRanged context hc second h.2⟩
  | .ite condition thenBranch elseBranch, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc condition h.1,
        structCompileProg_byteRanged context hc thenBranch h.2.1,
        structCompileProg_byteRanged context hc elseBranch h.2.2⟩
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc condition h.1,
        structCompileProg_byteRanged context hc body h.2⟩
  | .break, _ => by simp [ProgByteRanged, structCompileProg]
  | .continue, _ => by simp [ProgByteRanged, structCompileProg]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, _⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, ⟨structCompileProgExps_byteRanged context hc arguments hargs, trivial⟩⟩
  | .call (some (kindOpt, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, hkind, _⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileProgExps_byteRanged context hc arguments hargs,
        hkind, trivial⟩
  | .call (some (kindOpt, some (exception, handlerVar, body))) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, hkind, hexception, hhandlerVar, hbody⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileProgExps_byteRanged context hc arguments hargs,
        hkind, hexception, hhandlerVar,
        structCompileProg_byteRanged context hc body hbody⟩
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, hf, hargs, hbody⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileShape_byteRanged context.structs shape hc hs, hf,
        structCompileProgExps_byteRanged context hc arguments hargs,
        structCompileProg_byteRanged { context with locals := (name, shape) :: context.locals }
          hc body hbody⟩
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc configuration h.2.1,
        structCompileExp_byteRanged context hc configurationLength h.2.2.1,
        structCompileExp_byteRanged context hc array h.2.2.2.1,
        structCompileExp_byteRanged context hc arrayLength h.2.2.2.2⟩
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc value h.2⟩
  | .return value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact structCompileExp_byteRanged context hc value h
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc address h.2⟩
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .tick, _ => by simp [ProgByteRanged, structCompileProg]
  | .annot tag text, h => by simpa [ProgByteRanged, structCompileProg] using h
termination_by program _ => sizeOf program
decreasing_by
  all_goals
    first
    | decreasing_trivial
    | (simp_wf; omega)
    | omega

private theorem structCompileProgExps_eq_of_shape_eq {width : Nat} [BEq String]
    (context : StructPassContext) (compileShape : StructContext → Shape → Shape)
    (hshape : ∀ shape, ShapeByteRanged shape →
      compileShape context.structs shape = structCompileShape context.structs shape) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        structCompileProg.structCompileExps context expressions compileShape =
          structCompileProg.structCompileExps context expressions
  | [], _ => by simp [structCompileProg.structCompileExps]
  | expression :: expressions, hall => by
      simp only [structCompileProg.structCompileExps]
      congr 1
      · exact structCompileExp_eq_of_shape_eq context compileShape hshape expression
          (hall expression (by simp))
      · exact structCompileProgExps_eq_of_shape_eq context compileShape hshape expressions
          (fun item hitem => hall item (by simp [hitem]))

private theorem structCompileProg_eq_of_shape_eq {width : Nat} [BEq String]
    (context : StructPassContext) (compileShape : StructContext → Shape → Shape)
    (hshape : ∀ shape, ShapeByteRanged shape →
      compileShape context.structs shape = structCompileShape context.structs shape) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      structCompileProg context program compileShape = structCompileProg context program
  | .skip, _ => by simp [structCompileProg]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨_, hshapeProg, hvalue, hbody⟩
      simp only [structCompileProg]
      rw [hshape shape hshapeProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value hvalue]
      rw [structCompileProg_eq_of_shape_eq
        { context with locals := (name, shape) :: context.locals } compileShape hshape body hbody]
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileProgExps_eq_of_shape_eq context compileShape hshape arguments h.2]
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape address h.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape address h.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape address h.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape first h.1]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape second h.2]
  | .ite condition thenBranch elseBranch, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape condition h.1]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape thenBranch h.2.1]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape elseBranch h.2.2]
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape condition h.1]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape body h.2]
  | .break, _ => by simp [structCompileProg]
  | .continue, _ => by simp [structCompileProg]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileProgExps_eq_of_shape_eq context compileShape hshape arguments h.2.1]
  | .call (some (returns, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileProgExps_eq_of_shape_eq context compileShape hshape arguments h.2.1]
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨_, hargs, _, _, _, hhandler⟩
      simp only [structCompileProg]
      rw [structCompileProgExps_eq_of_shape_eq context compileShape hshape arguments hargs]
      rw [structCompileProg_eq_of_shape_eq context compileShape hshape handler hhandler]
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨_, hshapeProg, _, hargs, hbody⟩
      simp only [structCompileProg]
      rw [hshape shape hshapeProg]
      rw [structCompileProgExps_eq_of_shape_eq context compileShape hshape arguments hargs]
      rw [structCompileProg_eq_of_shape_eq
        { context with locals := (name, shape) :: context.locals } compileShape hshape body hbody]
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape configuration h.2.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape configurationLength h.2.2.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape array h.2.2.2.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape arrayLength h.2.2.2.2]
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .return value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h]
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape address h.2]
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape address h.1]
      rw [structCompileExp_eq_of_shape_eq context compileShape hshape value h.2]
  | .tick, _ => by simp [structCompileProg]
  | .annot tag text, _ => by simp [structCompileProg]
termination_by program _ => sizeOf program
decreasing_by
  all_goals
    first
    | decreasing_trivial
    | (simp_wf; omega)
    | omega

private theorem structGetNamesStep_ctxBR {width : Nat} (context : StructPassContext)
    (declaration : Decl (BitVec width)) (hc : CtxBR context.structs)
    (hd : DeclByteRanged declaration) :
    CtxBR ((match declaration with
      | .name name fields =>
          { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
      | _ => context).structs) := by
  cases declaration with
  | name name fields =>
      simp only [DeclByteRanged] at hd
      intro pair hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · cases hp
        exact ⟨hd.1, hd.2⟩
      · exact hc pair hp
  | decl shape name value => exact hc
  | function declaration => exact hc
  | exnDecl exception shape => exact hc

private theorem structCompileParams_byteRanged [BEq String] (context : StructContext)
    (hc : CtxBR context) (parameters : List (String × Shape))
    (h : ListParamByteRanged parameters) :
    ListParamByteRanged (parameters.map fun (name, shape) =>
      (name, structCompileShape context shape)) := by
  intro parameter hmem
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
  rcases h source hsource with ⟨hname, hshape⟩
  exact ⟨hname, structCompileShape_byteRanged context source.2 hc hshape⟩

/-- Flapjack range infrastructure: any selected association-list payload
satisfies an invariant held by all source entries. No HOL theorem is claimed. -/
theorem lookupInfo_payload_invariant {α : Type} (property : α → Prop)
    (key : String) (entries : List (String × α))
    (hall : ∀ p ∈ entries, property p.2) (value : α)
    (hlookup : lookupInfo key entries = some value) : property value := by
  induction entries with
  | nil => simp [lookupInfo] at hlookup
  | cons entry entries ih =>
      rcases entry with ⟨candidate, payload⟩
      by_cases hmatch : candidate == key
      · simp only [lookupInfo, hmatch] at hlookup
        cases hlookup
        exact hall (candidate, value) (by simp)
      · simp only [lookupInfo, hmatch] at hlookup
        exact ih (fun p hp => hall p (by simp [hp])) hlookup

private theorem lookupShape_default_byteRanged (name : String) (entries : List (String × Shape))
    (hall : ListParamByteRanged entries) :
    ShapeByteRanged ((lookupInfo name entries).getD .one) := by
  cases hlookup : lookupInfo name entries with
  | none => simp [ShapeByteRanged]
  | some shape =>
      exact lookupInfo_payload_invariant ShapeByteRanged name entries
        (fun p hp => (hall p hp).2) shape hlookup

private theorem shapeToHOL_getD_map (value : Option Shape) :
    (value.map shapeToHOL).getD .one = shapeToHOL (value.getD .one) := by
  cases value <;> simp [Option.getD, shapeToHOL]

private theorem structOldExpShapes_eq_map {α : Type} (context : StructPassContext)
    (expressions : List (Exp α)) :
    structOldExpShape.structOldExpShapes context expressions =
      expressions.map (structOldExpShape context) := by
  induction expressions with
  | nil => simp [structOldExpShape.structOldExpShapes]
  | cons expression expressions ih => simp [structOldExpShape.structOldExpShapes, ih]

end Flapjack
