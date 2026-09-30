import Flapjack.Pancake.PanStructs
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanStructs.CompileShapeExact
import Flapjack.Pancake.PanStructs.OldExpShapeExact

/-!
Byte-rangedness preservation for the named-structure elimination pass
(`structCompileTop`). The pass rewrites every shape in a declaration through
`structCompileShape`, so proving `DeclByteRanged` survives it needs
byte-rangedness of the struct shapes, the compiled expressions, and the
compiled programs, carried by the struct context invariant `CtxBR`.

Nothing here is a HOL port; the definitions already live in `PanStructs.lean`,
and these lemmas are Flapjack-specific infrastructure for the executed
parser-to-Crep boundary.
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

/-- Exact HOL-shape callback for the parser-proved struct pass. This function
    is only exported through `structCompileTopExactOfByteRanged` below, whose
    source premise is required because the total String-to-MlString codec is
    lossy outside `NameRanged`. -/
def structCompileShapeExactProduction (context : StructContext) (shape : Shape) : Shape :=
  shapeOfHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact
    (structContextToCompileShapeExact context) (shapeToHOL shape))

/-- The callback-driven exact `pan_structs` pass, restricted to declaration
    lists that round-trip through the HOL byte-valued name and shape carriers.
    `structCompileTopExact_eq_legacyOfByteRanged` proves its output equals the
    legacy pass on this domain. The parser-backed `compileFlapjackEntryCake`
    route executes this pass after composing its byte-range evidence. This
    codec wrapper has no separate HOL declaration. -/
def structCompileTopExactOfByteRanged [BEq String] {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (_hdeclarations : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (Decl (BitVec width)) :=
  structCompileTop declarations structCompileShapeExactProduction

theorem structCompileShape_byteRanged (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    ShapeByteRanged (structCompileShape context shape) :=
  structCompileShapeWF_byteRanged context shape hc hs

theorem structCompileShapesWF_byteRanged (context : StructContext) (hc : CtxBR context)
    (shapes : List Shape) (hs : ∀ s ∈ shapes, ShapeByteRanged s) :
    ∀ s ∈ structCompileShapeWF.structCompileShapesWF context shapes, ShapeByteRanged s := by
  induction shapes with
  | nil => intro s hmem; simp [structCompileShapeWF.structCompileShapesWF] at hmem
  | cons shape shapes ih =>
      intro s hmem
      simp only [structCompileShapeWF.structCompileShapesWF] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact structCompileShapeWF_byteRanged context shape hc (hs shape (by simp))
      · exact ih (fun t ht => hs t (by simp [ht])) s hmem'

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
      (compileShape : StructContext → Shape → Shape),
      compileShape = structCompileShape → ExpByteRanged e →
        ExpByteRanged (structCompileExp context e compileShape) := by
    exact (structCompileExp.induct (α := BitVec width) context
    (motive1 := fun l compileShape => compileShape = structCompileShape →
        (∀ e ∈ l, ExpByteRanged e) →
          ∀ e ∈ structCompileExp.structCompileExps context l compileShape, ExpByteRanged e)
    (motive2 := fun e compileShape => compileShape = structCompileShape →
        ExpByteRanged e → ExpByteRanged (structCompileExp context e compileShape))
    (motive3 := fun l compileShape => compileShape = structCompileShape →
        (∀ p ∈ l, ExpByteRanged p.2) →
          ∀ p ∈ structCompileExp.structCompileFields context l compileShape, ExpByteRanged p.2)
    (by
      intro compileShape hcb hall e he
      simp [structCompileExp.structCompileExps] at he)
    (by
    intro e es compileShape ihe ihes hcb hall x hx
    simp only [structCompileExp.structCompileExps] at hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ihe hcb (hall e (by simp))
    · exact ihes hcb (fun y hy => hall y (by simp [hy])) x hx')
    (by
      intro fields compileShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro index value compileShape ih hcb hv
      rw [structCompileExp]
      simp only [ExpByteRanged] at hv ⊢
      exact ih hcb hv)
    (by
      intro name fields compileShape info hlookup ihfields hcb hv
      rw [structCompileExp]
      simp only [hlookup]
      exact (listExpByteRanged_iff _).mpr
        (structSelectFields_byteRanged info.fields _
          (ihfields hcb (fun p hp => ((listFieldByteRanged_iff fields).mp hv.2 p hp).2))))
    (by
      intro name fields compileShape hlookup ihfields hcb _hv
      rw [structCompileExp]
      simp only [hlookup]
      simp [ExpByteRanged, ListExpByteRanged])
    (by
      intro field value compileShape ih hcb hv
      rw [structCompileExp]
      simp only [ExpByteRanged] at hv ⊢
      exact ih hcb hv.2)
    (by
      intro shape address compileShape ih hcb hv
      rw [structCompileExp]
      subst compileShape
      exact ⟨structCompileShape_byteRanged context.structs shape hc hv.1, ih rfl hv.2⟩)
    (by
      intro address compileShape ih hcb hv
      rw [structCompileExp]
      exact ih hcb hv)
    (by
      intro address compileShape ih hcb hv
      rw [structCompileExp]
      exact ih hcb hv)
    (by
      intro operator arguments compileShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator arguments compileShape ih hcb hv
      rw [structCompileExp]
      exact (listExpByteRanged_iff _).mpr (ih hcb ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator left right compileShape ihl ihr hcb hv
      rw [structCompileExp]
      exact ⟨ihl hcb hv.1, ihr hcb hv.2⟩)
    (by
      intro operator left right compileShape ihl ihr hcb hv
      rw [structCompileExp]
      exact ⟨ihl hcb hv.1, ihr hcb hv.2⟩)
    (by
      intro compileShape expression h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hcb hv
      subst compileShape
      cases expression with
      | const v => simp [ExpByteRanged]
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
      intro compileShape hcb _ p hp
      simp [structCompileExp.structCompileFields] at hp)
    (by
      intro field expression fields compileShape ihe ih hcb hall p hp
      simp only [structCompileExp.structCompileFields] at hp
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact ihe hcb (hall (field, expression) (by simp))
      · exact ih hcb (fun q hq => hall q (by simp [hq])) p hp'))
  intro e he
  exact hgeneral e structCompileShape rfl he

private theorem structCompileExp_eq_of_shape_eq {width : Nat} [BEq String]
    (context : StructPassContext) (compileShape : StructContext → Shape → Shape) :
    (∀ shape, ShapeByteRanged shape →
      compileShape context.structs shape = structCompileShape context.structs shape) →
    ∀ expression : Exp (BitVec width), ExpByteRanged expression →
      structCompileExp context expression compileShape = structCompileExp context expression := by
  have hgeneral : ∀ (expression : Exp (BitVec width))
      (compileShape : StructContext → Shape → Shape),
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      ExpByteRanged expression →
        structCompileExp context expression compileShape = structCompileExp context expression := by
    exact (structCompileExp.induct (α := BitVec width) context
    (motive1 := fun expressions compileShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        structCompileExp.structCompileExps context expressions compileShape =
          structCompileExp.structCompileExps context expressions)
    (motive2 := fun expression compileShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      ExpByteRanged expression →
        structCompileExp context expression compileShape = structCompileExp context expression)
    (motive3 := fun fields compileShape =>
      (∀ shape, ShapeByteRanged shape →
        compileShape context.structs shape = structCompileShape context.structs shape) →
      (∀ field ∈ fields, ExpByteRanged field.2) →
        structCompileExp.structCompileFields context fields compileShape =
          structCompileExp.structCompileFields context fields)
    (by
      intro compileShape hshape hall
      simp [structCompileExp.structCompileExps])
    (by
      intro expression expressions compileShape ihe ih hshape hall
      simp only [structCompileExp.structCompileExps]
      rw [ihe hshape (hall expression (by simp))]
      rw [ih hshape (fun item hitem => hall item (by simp [hitem]))])
    (by
      intro fields compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.rStruct (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro index value compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.rField index) (ih hshape hv))
    (by
      intro name fields compileShape info hlookup ih hshape hv
      simp only [structCompileExp, hlookup]
      rw [ih hshape (fun field hfield =>
        ((listFieldByteRanged_iff fields).mp hv.2 field hfield).2)])
    (by
      intro name fields compileShape hlookup ih hshape _hv
      simp only [structCompileExp, hlookup])
    (by
      intro field value compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.rField (match structOldExpShape context value with
        | .named name =>
            match lookupInfo name context.structs with
            | some info => (structFindFieldIndex field info.fields).getD 0
            | none => 0
        | _ => 0)) (ih hshape hv.2))
    (by
      intro shape address compileShape ih hshape hv
      simp only [structCompileExp]
      rw [hshape shape hv.1, ih hshape hv.2])
    (by
      intro address compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.load32 (ih hshape hv))
    (by
      intro address compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg Exp.loadByte (ih hshape hv))
    (by
      intro operator arguments compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.op operator) (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator arguments compileShape ih hshape hv
      simp only [structCompileExp]
      exact congrArg (Exp.panOp operator) (ih hshape ((listExpByteRanged_iff _).mp hv)))
    (by
      intro operator left right compileShape ihl ihr hshape hv
      simp only [structCompileExp]
      simp only [Exp.cmp.injEq]
      exact ⟨trivial, ihl hshape hv.1, ihr hshape hv.2⟩)
    (by
      intro operator left right compileShape ihl ihr hshape hv
      simp only [structCompileExp]
      simp only [Exp.shift.injEq]
      exact ⟨trivial, ihl hshape hv.1, ihr hshape hv.2⟩)
    (by
      intro compileShape expression h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hshape hv
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
      intro compileShape hshape hall
      simp [structCompileExp.structCompileFields])
    (by
      intro field expression fields compileShape ihe ih hshape hall
      simp only [structCompileExp.structCompileFields]
      simp only [ihe hshape (hall (field, expression) (by simp)),
        ih hshape (fun pair hpair => hall pair (by simp [hpair]))]))
  intro hshape expression he
  exact hgeneral expression compileShape hshape he

private theorem structCompileShapeExactProduction_eq_legacy
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

private theorem structCompileParams_byteRanged [BEq String] (context : StructContext)
    (hc : CtxBR context) (parameters : List (String × Shape))
    (h : ListParamByteRanged parameters) :
    ListParamByteRanged (parameters.map fun (name, shape) =>
      (name, structCompileShape context shape)) := by
  intro parameter hmem
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
  rcases h source hsource with ⟨hname, hshape⟩
  exact ⟨hname, structCompileShape_byteRanged context source.2 hc hshape⟩

private theorem structCompileParams_eq_of_shape_eq [BEq String] (context : StructContext)
    (compileShape : StructContext → Shape → Shape)
    (hshape : ∀ shape, ShapeByteRanged shape →
      compileShape context shape = structCompileShape context shape) :
    ∀ parameters : List (String × Shape), ListParamByteRanged parameters →
      parameters.map (fun (name, shape) => (name, compileShape context shape)) =
        parameters.map (fun (name, shape) => (name, structCompileShape context shape)) := by
  intro parameters
  induction parameters with
  | nil => simp
  | cons parameter parameters ih =>
      intro hall
      obtain ⟨name, shape⟩ := parameter
      obtain ⟨_, hs⟩ := hall (name, shape) (by simp)
      simp only [List.map_cons]
      rw [hshape shape hs]
      congr 1
      exact ih (fun item hitem => hall item (by simp [hitem]))

private theorem structCompileDecls_context_eq [BEq String]
    (declarations : List (Decl α)) :
    ∀ (context : StructPassContext) (firstShape secondShape : StructContext → Shape → Shape),
      (structCompileDecls declarations context firstShape).2 =
        (structCompileDecls declarations context secondShape).2 := by
  induction declarations with
  | nil => intro context firstShape secondShape; rfl
  | cons declaration rest ih =>
      intro context firstShape secondShape
      cases declaration with
      | decl shape name value =>
          simpa [structCompileDecls] using
            ih { context with globals := (name, shape) :: context.globals } firstShape secondShape
      | function declaration =>
          simpa [structCompileDecls] using ih context firstShape secondShape
      | exnDecl exception shape =>
          simpa [structCompileDecls] using ih context firstShape secondShape
      | name struct fields =>
          simpa [structCompileDecls] using ih context firstShape secondShape

private theorem structCompileDecls_structs {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width))) :
    ∀ context : StructPassContext,
      (structCompileDecls declarations context).2.structs = context.structs := by
  induction declarations with
  | nil => intro context; rfl
  | cons declaration rest ih =>
      intro context
      cases declaration <;> simp [structCompileDecls, ih]

private theorem structCompileProg_exact_eq_legacy {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      structCompileProg context program structCompileShapeExactProduction =
        structCompileProg context program := by
  apply structCompileProg_eq_of_shape_eq context structCompileShapeExactProduction
  intro shape hshape
  exact structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape

private theorem structCompileDeclsExact_eq_legacy {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width))) :
    ∀ (context : StructPassContext), CtxBR context.structs →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
        (structCompileDecls declarations context structCompileShapeExactProduction).1 =
          (structCompileDecls declarations context).1 := by
  induction declarations with
  | nil => intro context hc hdecls; rfl
  | cons declaration rest ih =>
      intro context hc hdecls
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | decl shape name value =>
          simp only [structCompileDecls]
          simp only [DeclByteRanged] at hd
          rcases hd with ⟨hshape, _, hvalue⟩
          rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
          rw [structCompileExp_exact_eq_legacy context hc value hvalue]
          congr 1
          exact ih { context with globals := (name, shape) :: context.globals } hc hrest
      | function declaration =>
          simp only [structCompileDecls]
          simp only [DeclByteRanged, FunDeclByteRanged] at hd
          rcases hd with ⟨_, hparams, hbody, hreturn⟩
          have htailContext := structCompileDecls_context_eq rest context
            structCompileShapeExactProduction structCompileShape
          have htailStructs := structCompileDecls_structs rest context
          have hcTail : CtxBR (structCompileDecls rest context).2.structs := by
            rw [htailStructs]
            exact hc
          have hparamsEq := structCompileParams_eq_of_shape_eq context.structs
            structCompileShapeExactProduction
            (fun shape hs => structCompileShapeExactProduction_eq_legacy
              context.structs shape hc hs) declaration.params hparams
          have hreturnEq := structCompileShapeExactProduction_eq_legacy
            context.structs declaration.returnShape hc hreturn
          have hbodyEq :
              structCompileProg
                  { (structCompileDecls rest context structCompileShapeExactProduction).2 with
                    locals := declaration.params }
                  declaration.body structCompileShapeExactProduction =
                structCompileProg
                  { (structCompileDecls rest context).2 with locals := declaration.params }
                  declaration.body := by
            rw [htailContext]
            exact structCompileProg_exact_eq_legacy
              { (structCompileDecls rest context).2 with locals := declaration.params }
              (by simpa [htailStructs] using hcTail) declaration.body hbody
          have hfunction :
              ({ declaration with
                params := declaration.params.map (fun (name, shape) =>
                  (name, structCompileShapeExactProduction context.structs shape))
                body := structCompileProg
                  { (structCompileDecls rest context structCompileShapeExactProduction).2 with
                    locals := declaration.params }
                  declaration.body structCompileShapeExactProduction
                returnShape := structCompileShapeExactProduction context.structs declaration.returnShape }) =
              ({ declaration with
                params := declaration.params.map (fun (name, shape) =>
                  (name, structCompileShape context.structs shape))
                body := structCompileProg
                  { (structCompileDecls rest context).2 with locals := declaration.params }
                  declaration.body
                returnShape := structCompileShape context.structs declaration.returnShape }) := by
            cases declaration with
            | mk name inline exported params body returnShape =>
                simp only [hparamsEq, hbodyEq, hreturnEq]
          rw [hfunction]
          rw [ih context hc hrest]
      | exnDecl exception shape =>
          simp only [structCompileDecls]
          simp only [DeclByteRanged] at hd
          rcases hd with ⟨_, hshape⟩
          rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
          congr 1
          exact ih context hc hrest
      | name struct fields =>
          simp only [structCompileDecls]
          exact ih context hc hrest

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

private theorem structGetNames_ctxBR {width : Nat} (context : StructPassContext)
    (declarations : List (Decl (BitVec width))) (hc : CtxBR context.structs)
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    CtxBR (structGetNames context declarations).structs := by
  induction declarations generalizing context with
  | nil => simpa [structGetNames] using hc
  | cons declaration rest ih =>
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | name name fields =>
          have hnext := structGetNamesStep_ctxBR context (.name name fields) hc hd
          change CtxBR (structGetNames
            { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
            rest).structs
          exact ih _ hnext hrest
      | decl shape name value =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest
      | function declaration =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest
      | exnDecl exception shape =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest

private theorem structCompileDecls_byteRanged {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width))) :
    ∀ context : StructPassContext, CtxBR context.structs →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      ∀ declaration ∈ (structCompileDecls declarations context).1,
        DeclByteRanged declaration := by
  induction declarations with
  | nil => simp [structCompileDecls]
  | cons declaration rest ih =>
      intro context hc hdecls result hresult
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | decl shape name value =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged] at hd ⊢
            rcases hd with ⟨hshape, hname, hvalue⟩
            exact ⟨structCompileShape_byteRanged context.structs shape hc hshape,
              hname, structCompileExp_byteRanged context hc value hvalue⟩
          · exact ih { context with globals := (name, shape) :: context.globals }
              hc hrest result htail
      | function declaration =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged, FunDeclByteRanged] at hd ⊢
            rcases hd with ⟨hname, hparams, hbody, hreturn⟩
            have hstructs := structCompileDecls_structs rest context
            have hctx : CtxBR (structCompileDecls rest context).2.structs := by
              simpa [hstructs] using hc
            have hbodyOut := structCompileProg_byteRanged
              { (structCompileDecls rest context).2 with locals := declaration.params }
              hctx declaration.body hbody
            refine ⟨hname, structCompileParams_byteRanged context.structs hc
              declaration.params hparams, ?_,
              structCompileShape_byteRanged context.structs declaration.returnShape hc hreturn⟩
            simpa [structCompileDecls, hstructs] using hbodyOut
          · exact ih context hc hrest result htail
      | exnDecl exception shape =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged] at hd ⊢
            rcases hd with ⟨hname, hshape⟩
            exact ⟨hname, structCompileShape_byteRanged context.structs shape hc hshape⟩
          · exact ih context hc hrest result htail
      | name name fields =>
          simp only [structCompileDecls] at hresult
          exact ih context hc hrest result hresult

theorem structCompileTop_byteRanged {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ structCompileTop declarations, DeclByteRanged declaration := by
  let initial : StructPassContext := { structs := [], locals := [], globals := [] }
  have hcontext : CtxBR (structGetNames initial declarations).structs :=
    structGetNames_ctxBR initial declarations (by simp [initial, CtxBR]) hdecls
  intro declaration hmem
  letI : BEq String := instBEqOfDecidableEq
  simpa [structCompileTop, initial] using
    structCompileDecls_byteRanged declarations (structGetNames initial declarations)
      hcontext hdecls declaration hmem

/-- On declarations supplied with parser byte-range evidence, routing the exact
    HOL `compile_shape` callback through every recursive shape site of
    `structCompileTop` produces the same declarations as the legacy callback.
    This Flapjack-specific compatibility theorem does not tag either pass as a
    HOL port; it discharges the whole-pass equality prerequisite for the
    production-route migration. -/
theorem structCompileTopExact_eq_legacyOfByteRanged {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width)))
    (hdeclarations : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    structCompileTopExactOfByteRanged declarations hdeclarations =
      structCompileTop declarations := by
  let initial : StructPassContext := { structs := [], locals := [], globals := [] }
  letI : BEq String := instBEqOfDecidableEq
  have hcontext : CtxBR (structGetNames initial declarations).structs :=
    structGetNames_ctxBR initial declarations (by simp [initial, CtxBR]) hdeclarations
  simpa [structCompileTopExactOfByteRanged, structCompileTop, initial] using
    structCompileDeclsExact_eq_legacy declarations (structGetNames initial declarations)
      hcontext hdeclarations


/-- Flapjack codec infrastructure, with no HOL original: encode all three
production context fields without cached StructInfo sizes. -/
def structPassContextToExact (context : StructPassContext) :
    Flapjack.Pancake.PanStructs.CompileShapeExact.ContextExact :=
  { structs := structContextToCompileShapeExact context.structs
    locals := context.locals.map fun p => (ofString p.1, shapeToHOL p.2)
    globals := context.globals.map fun p => (ofString p.1, shapeToHOL p.2) }

/-- Flapjack codec infrastructure, not a HOL theorem. Byte-range hypotheses
ensure exact identifier equality selects the same first occurrence, including
missing keys and duplicate keys, for any translated payload. -/
theorem encodedContextLookup {α β : Type} (convert : α → β)
    (name : String) (entries : List (String × α))
    (hname : NameRanged name) (hkeys : ∀ p ∈ entries, NameRanged p.1) :
    (entries.map fun p => (ofString p.1, convert p.2)).findSome?
        (fun p => if p.1 = ofString name then some p.2 else none) =
      (lookupInfo name entries).map convert := by
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, value⟩
      have hcandidate := hkeys (candidate, value) (by simp)
      have htail : ∀ p ∈ entries, NameRanged p.1 :=
        fun p hp => hkeys p (by simp [hp])
      by_cases hmatch : candidate = name
      · subst candidate
        simp [lookupInfo]
      · have hexact : ofString candidate ≠ ofString name :=
          fun h => hmatch (ofString_injective_of_ranged_local hcandidate hname h)
        simp [lookupInfo, hmatch, hexact, ih htail]

/-- Flapjack codec lookup specialization for source local/global/field shapes;
shape payload conversion preserves every source shape. -/
theorem encodedShapeContextLookup (name : String) (entries : List (String × Shape))
    (hname : NameRanged name) (hentries : ListParamByteRanged entries) :
    (entries.map fun p => (ofString p.1, shapeToHOL p.2)).findSome?
        (fun p => if p.1 = ofString name then some p.2 else none) =
      (lookupInfo name entries).map shapeToHOL := by
  exact encodedContextLookup shapeToHOL name entries hname
    (fun p hp => (hentries p hp).1)


/-- Flapjack codec infrastructure: the exact local lookup is the source lookup
with its shape payload encoded, under the actual byte-range obligations. -/
theorem structPassContextToExact_locals (context : StructPassContext) (name : String)
    (hname : NameRanged name) (hentries : ListParamByteRanged context.locals) :
    (structPassContextToExact context).locals.findSome?
        (fun p => if p.1 = ofString name then some p.2 else none) =
      (lookupInfo name context.locals).map shapeToHOL :=
  encodedShapeContextLookup name context.locals hname hentries

/-- Flapjack codec infrastructure: the exact global lookup preserves the
source first-match result and all missing-key defaults. -/
theorem structPassContextToExact_globals (context : StructPassContext) (name : String)
    (hname : NameRanged name) (hentries : ListParamByteRanged context.globals) :
    (structPassContextToExact context).globals.findSome?
        (fun p => if p.1 = ofString name then some p.2 else none) =
      (lookupInfo name context.globals).map shapeToHOL :=
  encodedShapeContextLookup name context.globals hname hentries

/-- Flapjack codec infrastructure: nested struct/field lookup preserves both
first-match searches. Missing structs or fields remain NONE; stored shape
payloads use the existing exact shape codec. -/
theorem encodedStructFieldLookup (context : StructContext) (name field : String)
    (hc : CtxBR context) (hname : NameRanged name) (hfield : NameRanged field) :
    ((structContextToCompileShapeExact context).findSome?
        (fun p => if p.1 = ofString name then some p.2 else none)).bind
        (fun fields => fields.findSome?
          (fun p => if p.1 = ofString field then some p.2 else none)) =
      ((lookupInfo name context).bind (fun info => lookupInfo field info.fields)).map
        shapeToHOL := by
  induction context with
  | nil => simp [structContextToCompileShapeExact, lookupInfo]
  | cons entry context ih =>
      rcases entry with ⟨candidate, info⟩
      have hhead := hc (candidate, info) (by simp)
      have htail : CtxBR context := fun p hp => hc p (by simp [hp])
      by_cases hmatch : candidate = name
      · subst candidate
        simpa [structContextToCompileShapeExact, lookupInfo] using
          encodedShapeContextLookup field info.fields hfield hhead.2
      · have hexact : ofString candidate ≠ ofString name :=
          fun h => hmatch (ofString_injective_of_ranged_local hhead.1 hname h)
        simpa [structContextToCompileShapeExact, lookupInfo, hmatch, hexact] using ih htail

/-- Flapjack codec infrastructure: decoding a looked-up encoded shape recovers
its production payload, rather than only relating the encoded maps. -/
theorem encodedShapeContextLookup_roundtrip (name : String)
    (entries : List (String × Shape)) (hname : NameRanged name)
    (hentries : ListParamByteRanged entries) :
    ((entries.map fun p => (ofString p.1, shapeToHOL p.2)).findSome?
      (fun p => if p.1 = ofString name then some p.2 else none)).map shapeOfHOL =
      lookupInfo name entries := by
  rw [encodedShapeContextLookup name entries hname hentries]
  induction entries with
  | nil => simp [lookupInfo]
  | cons entry entries ih =>
      rcases entry with ⟨candidate, shape⟩
      have hhead := hentries (candidate, shape) (by simp)
      have htail : ListParamByteRanged entries := fun p hp => hentries p (by simp [hp])
      by_cases hmatch : candidate = name
      · simp [lookupInfo, hmatch, shapeOfHOL_shapeToHOL shape hhead.2]
      · simpa [lookupInfo, hmatch] using ih htail

/-- Flapjack range infrastructure: any selected association-list payload
satisfies an invariant held by all source entries. No HOL theorem is claimed. -/
private theorem lookupInfo_payload_invariant {α : Type} (property : α → Prop)
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

mutual
  /-- Flapjack codec prerequisite, not a HOL theorem. Derives the range of the
  computed source shape from real source input/context invariants; in particular
  a computed Named name can safely be used by the exact lookup correspondence. -/
  theorem structOldExpShape_byteRanged {width : Nat} (context : StructPassContext)
      (hc : CtxBR context.structs) (hl : ListParamByteRanged context.locals)
      (hg : ListParamByteRanged context.globals) (expression : Exp (BitVec width))
      (he : ExpByteRanged expression) : ShapeByteRanged (structOldExpShape context expression) := by
    cases hexpression : expression with
    | var kind name =>
        cases kind
        · simpa only [structOldExpShape] using lookupShape_default_byteRanged name context.locals hl
        · simpa only [structOldExpShape] using lookupShape_default_byteRanged name context.globals hg
    | rStruct fields =>
        simp only [hexpression, ExpByteRanged] at he
        simpa only [structOldExpShape, ShapeByteRanged] using
          structOldExpShapes_byteRanged context hc hl hg fields ((listExpByteRanged_iff fields).mp he)
    | rField index value =>
        simp only [hexpression, ExpByteRanged] at he
        have hshape := structOldExpShape_byteRanged context hc hl hg value he
        cases hvalue : structOldExpShape context value with
        | one => simp [structOldExpShape, hvalue, ShapeByteRanged]
        | named name => simp [structOldExpShape, hvalue, ShapeByteRanged]
        | comb shapes =>
            simp only [hvalue, ShapeByteRanged] at hshape
            simp only [structOldExpShape, hvalue]
            cases hindex : shapes[index]? with
            | none => simp [List.getD, hindex, ShapeByteRanged]
            | some shape =>
                have hmem : shape ∈ shapes := List.mem_of_getElem? hindex
                simpa [List.getD, hindex] using hshape shape hmem
    | nStruct name fields =>
        simp only [hexpression, ExpByteRanged] at he
        simpa only [structOldExpShape, ShapeByteRanged] using he.1
    | nField field value =>
        cases hvalue : structOldExpShape context value with
        | one => simp [structOldExpShape, hvalue, ShapeByteRanged]
        | comb shapes => simp [structOldExpShape, hvalue, ShapeByteRanged]
        | named name =>
            simp only [structOldExpShape, hvalue]
            cases hlookup : lookupInfo name context.structs with
            | none => simp [ShapeByteRanged]
            | some info =>
                have hfields : ListParamByteRanged info.fields :=
                  lookupInfo_payload_invariant (fun info : StructInfo => ListParamByteRanged info.fields)
                    name context.structs (fun p hp => (hc p hp).2) info hlookup
                have hr := lookupShape_default_byteRanged field info.fields hfields
                cases hf : lookupInfo field info.fields <;> simpa [hf] using hr
    | load shape address =>
        simp only [hexpression, ExpByteRanged] at he
        simpa only [structOldExpShape] using he.1
    | const value => simp [structOldExpShape, ShapeByteRanged]
    | load32 address => simp [structOldExpShape, ShapeByteRanged]
    | loadByte address => simp [structOldExpShape, ShapeByteRanged]
    | op operator args => simp [structOldExpShape, ShapeByteRanged]
    | panOp operator args => simp [structOldExpShape, ShapeByteRanged]
    | cmp operator left right => simp [structOldExpShape, ShapeByteRanged]
    | shift operator left right => simp [structOldExpShape, ShapeByteRanged]
    | baseAddr => simp [structOldExpShape, ShapeByteRanged]
    | topAddr => simp [structOldExpShape, ShapeByteRanged]
    | bytesInWord => simp [structOldExpShape, ShapeByteRanged]
  termination_by sizeOf expression
  decreasing_by all_goals simp_all; all_goals omega

  /-- Flapjack range infrastructure for the mutual expression-list worker. -/
  theorem structOldExpShapes_byteRanged {width : Nat} (context : StructPassContext)
      (hc : CtxBR context.structs) (hl : ListParamByteRanged context.locals)
      (hg : ListParamByteRanged context.globals) (expressions : List (Exp (BitVec width)))
      (he : ∀ e ∈ expressions, ExpByteRanged e) :
      ∀ shape ∈ structOldExpShape.structOldExpShapes context expressions, ShapeByteRanged shape := by
    cases hexpressions : expressions with
    | nil => simp [structOldExpShape.structOldExpShapes]
    | cons expression expressions =>
        rw [hexpressions] at he
        intro shape hmem
        simp only [structOldExpShape.structOldExpShapes] at hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact structOldExpShape_byteRanged context hc hl hg expression (he expression (by simp))
        · exact structOldExpShapes_byteRanged context hc hl hg expressions
            (fun e h => he e (by simp [h])) shape htail
  termination_by sizeOf expressions
  decreasing_by all_goals simp_all; all_goals omega
end

/-- Flapjack codec infrastructure for raw field selection. Encoding commutes
with indexed selection and the defensive One default, including out-of-range
indices. This representation lemma has no HOL theorem original. -/
theorem shapeToHOL_getD (shapes : List Shape) (index : Nat) :
    shapeToHOL (shapes.getD index .one) =
      (shapes.map shapeToHOL)[index]?.getD .one := by
  induction shapes generalizing index with
  | nil => simp [List.getD, shapeToHOL]
  | cons shape shapes ih =>
      cases index with
      | zero => simp [List.getD]
      | succ index => simpa [List.getD] using ih index

/-- Flapjack cross-carrier infrastructure: both source variable kinds retain
first-match lookup and the One default. The source name is actually ranged;
no successful lookup or computed result is assumed. No HOL theorem original. -/
theorem oldExpShapeExact_var_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (kind : VarKind) (name : String)
    (hn : NameRanged name) (hl : ListParamByteRanged context.locals)
    (hg : ListParamByteRanged context.globals) :
    Pancake.PanStructs.CompileShapeExact.oldExpShapeExact
      (structPassContextToExact context) (expToHOL (Exp.var kind name : Exp (BitVec width))) =
        shapeToHOL (structOldExpShape context (Exp.var kind name : Exp (BitVec width))) := by
  cases kind
  · simp only [expToHOL, Pancake.PanStructs.CompileShapeExact.oldExpShapeExact,
      structOldExpShape]
    rw [structPassContextToExact_locals context name hn hl]
    cases lookupInfo name context.locals <;> simp [shapeToHOL]
  · simp only [expToHOL, Pancake.PanStructs.CompileShapeExact.oldExpShapeExact,
      structOldExpShape]
    rw [structPassContextToExact_globals context name hn hg]
    cases lookupInfo name context.globals <;> simp [shapeToHOL]

/-- Flapjack codec equation for the source Named constructor. Its payload
expressions do not affect the old shape; no HOL theorem original. -/
theorem oldExpShapeExact_nStruct_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (name : String)
    (fields : List (String × Exp (BitVec width))) :
    Pancake.PanStructs.CompileShapeExact.oldExpShapeExact
      (structPassContextToExact context) (expToHOL (.nStruct name fields)) =
        shapeToHOL (structOldExpShape context (.nStruct name fields)) := by
  simp only [expToHOL, Pancake.PanStructs.CompileShapeExact.oldExpShapeExact,
    structOldExpShape, shapeToHOL]

/-- Flapjack codec equation for the source Load constructor: its explicit
shape is retained without evaluating the address; no HOL theorem original. -/
theorem oldExpShapeExact_load_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (shape : Shape) (address : Exp (BitVec width)) :
    Pancake.PanStructs.CompileShapeExact.oldExpShapeExact
      (structPassContextToExact context) (expToHOL (.load shape address)) =
        shapeToHOL (structOldExpShape context (.load shape address)) := by
  simp only [expToHOL, Pancake.PanStructs.CompileShapeExact.oldExpShapeExact,
    structOldExpShape]

/-- Flapjack codec infrastructure for compile_exp named-field indexing.
Actual byte-ranged query and stored names make equality injective through the
name codec. Both operations retain the first duplicate match and absent fields;
this cross-carrier lemma has no HOL theorem original. -/
theorem encodedFieldIndexLookup (field : String) (fields : List (String × Shape))
    (hfield : NameRanged field) (hfields : ListParamByteRanged fields) :
    afindi (ofString field) (fields.map fun p => (ofString p.1, shapeToHOL p.2)) =
      structFindFieldIndex field fields := by
  induction fields with
  | nil => simp [afindi, structFindFieldIndex]
  | cons entry fields ih =>
      rcases entry with ⟨candidate, shape⟩
      have hhead := hfields (candidate, shape) (by simp)
      have htail : ListParamByteRanged fields := fun p hp => hfields p (by simp [hp])
      by_cases hmatch : candidate = field
      · subst candidate
        simp [afindi, structFindFieldIndex]
      · have hexact : ofString field ≠ ofString candidate :=
          fun h => hmatch (ofString_injective_of_ranged_local hhead.1 hfield h.symm)
        simp only [List.map_cons, afindi_cons, hexact, ↓reduceIte,
          structFindFieldIndex, beq_iff_eq, hmatch, ↓reduceIte]
        rw [ih htail]
        cases structFindFieldIndex field fields <;> rfl

/-- Flapjack codec corollary retaining the source zero default for missing
named fields. No target lookup success or index bounds are assumed. -/
theorem encodedFieldIndexLookup_default (field : String) (fields : List (String × Shape))
    (hfield : NameRanged field) (hfields : ListParamByteRanged fields) :
    (afindi (ofString field) (fields.map fun p => (ofString p.1, shapeToHOL p.2))).getD 0 =
      (structFindFieldIndex field fields).getD 0 := by
  rw [encodedFieldIndexLookup field fields hfield hfields]

end Flapjack
