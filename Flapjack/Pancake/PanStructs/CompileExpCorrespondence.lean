import Flapjack.Pancake.PanStructsByteRanged
import Flapjack.Pancake.PanStructs.CompileExpExact

/-! Flapjack codec infrastructure for this pass, with no HOL theorem original.
Correspondence requires the actual parser byte-range invariants rather than
assuming the compiler result or its simulation. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString

/-- Flapjack factoring of the reviewed recursive expression-list compiler. -/
theorem compileExpsExact_eq_map {width : Nat} [NeZero width]
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact)
    (expressions : List (ExpHOL width)) :
    Pancake.PanStructs.CompileShapeExact.compileExpsExact context expressions =
      expressions.map (Pancake.PanStructs.CompileShapeExact.compileExpExact context) := by
  induction expressions with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact]
  | cons expression expressions ih =>
      simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact, ih]

/-- Flapjack factoring: field compilation preserves every supplied key and
its order, including duplicates; only expression payloads are compiled. -/
theorem compileFieldsExact_eq_map {width : Nat} [NeZero width]
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact)
    (fields : List (MlS × ExpHOL width)) :
    Pancake.PanStructs.CompileShapeExact.compileFieldsExact context fields =
      fields.map (fun p =>
        (p.1, Pancake.PanStructs.CompileShapeExact.compileExpExact context p.2)) := by
  induction fields with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact]
  | cons field fields ih =>
      rcases field with ⟨name, expression⟩
      simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact, ih]

/-- Flapjack codec prerequisite: production field compilation preserves the
actual parser's key-range invariant for arbitrary shape callbacks. -/
theorem structCompileFields_keys_ranged {width : Nat}
    (context : StructPassContext) (fields : List (String × Exp (BitVec width)))
    (compileShape : StructContext → Shape → Shape)
    (oldShape : StructPassContext → Exp (BitVec width) → Shape)
    (hfields : ListFieldByteRanged fields) :
    ∀ p ∈ structCompileExp.structCompileFields context fields compileShape oldShape,
      NameRanged p.1 := by
  induction fields with
  | nil => simp [structCompileExp.structCompileFields]
  | cons field fields ih =>
      rcases field with ⟨name, expression⟩
      simp only [ListFieldByteRanged] at hfields
      intro p hp
      simp only [structCompileExp.structCompileFields, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hfields.1
      · exact ih hfields.2.2 p hp

/-- The exact named-structure selection preserves declaration order, the first
supplied occurrence of a duplicate key, and omissions. Payloads need no range
premise because this lemma only encodes them; identifier equality needs the
real byte-range premises. -/
theorem encodedStructSelectFields {width : Nat} [NeZero width]
    (fields : List (String × Shape)) (compiled : List (String × Exp (BitVec width)))
    (hfields : ListParamByteRanged fields)
    (hkeys : ∀ p ∈ compiled, NameRanged p.1) :
    (fields.map fun p => (ofString p.1, shapeToHOL p.2)).flatMap
        (fun p => match
          (compiled.map fun q => (ofString q.1, expToHOL q.2)).findSome?
            (fun q => if q.1 = p.1 then some q.2 else none) with
          | none => []
          | some value => [value]) =
      (structSelectFields fields compiled).map expToHOL := by
  induction fields with
  | nil => simp [structSelectFields]
  | cons entry fields ih =>
      rcases entry with ⟨field, shape⟩
      have hfield := hfields (field, shape) (by simp)
      have htail : ListParamByteRanged fields := fun p hp => hfields p (by simp [hp])
      have hlookup := encodedContextLookup expToHOL field compiled hfield.1 hkeys
      simp only [List.map_cons, List.flatMap_cons, hlookup, structSelectFields]
      cases h : lookupInfo field compiled <;> simp [ih htail]

/-- Flapjack recursive codec case: named projection uses the original source
expression's shape, the first declared field position, and default index zero.
The sole compiler equality premise is the recursive child's induction result. -/
theorem compileExpExact_nField_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (field : String) (value : Exp (BitVec width))
    (hc : CtxBR context.structs) (hl : ListParamByteRanged context.locals)
    (hg : ListParamByteRanged context.globals)
    (hf : NameRanged field) (hv : ExpByteRanged value)
    (ih : Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL value) =
      expToHOL (structCompileExp context value)) :
    Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL (.nField field value)) =
      expToHOL (structCompileExp context (.nField field value)) := by
  rw [expToHOL.eq_6, Pancake.PanStructs.CompileShapeExact.compileExpExact.eq_4]
  rw [ih, oldExpShapeExact_encode context value hc hl hg hv]
  cases hs : structOldExpShape context value with
  | one => simp [shapeToHOL, structCompileExp, hs, expToHOL]
  | comb shapes => simp [shapeToHOL, structCompileExp, hs, expToHOL]
  | named name =>
      have hn := structOldExpShape_byteRanged context hc hl hg value hv
      simp only [hs, ShapeByteRanged] at hn
      have hlookup := encodedContextLookup
        (fun info : StructInfo => info.fields.map fun p => (ofString p.1, shapeToHOL p.2))
        name context.structs hn (fun p hp => (hc p hp).1)
      cases hinfo : lookupInfo name context.structs with
      | none =>
          simp [shapeToHOL, structPassContextToExact, structContextToCompileShapeExact,
            hlookup, hinfo, structCompileExp, hs, expToHOL]
      | some info =>
          have hfields : ListParamByteRanged info.fields :=
            lookupInfo_payload_invariant (fun info : StructInfo => ListParamByteRanged info.fields)
              name context.structs (fun p hp => (hc p hp).2) info hinfo
          have hindex := encodedFieldIndexLookup_default field info.fields hf hfields
          simp [shapeToHOL, structPassContextToExact, structContextToCompileShapeExact,
            hlookup, hinfo, structCompileExp, hs, expToHOL, hindex]

/-- Flapjack recursive codec case for a named structure: the declaration's
field order drives selection of the first compiled supplied occurrence. The
premise is precisely the recursive supplied-field induction result. -/
theorem compileExpExact_nStruct_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (name : String)
    (fields : List (String × Exp (BitVec width)))
    (hc : CtxBR context.structs) (hn : NameRanged name)
    (hf : ListFieldByteRanged fields)
    (ih : Pancake.PanStructs.CompileShapeExact.compileFieldsExact
        (structPassContextToExact context)
        (fields.map fun p => (ofString p.1, expToHOL p.2)) =
      (structCompileExp.structCompileFields context fields).map
        (fun p => (ofString p.1, expToHOL p.2))) :
    Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL (.nStruct name fields)) =
      expToHOL (structCompileExp context (.nStruct name fields)) := by
  rw [expToHOL.eq_5, Pancake.PanStructs.CompileShapeExact.compileExpExact.eq_3, ih]
  have hlookup := encodedContextLookup
    (fun info : StructInfo => info.fields.map fun p => (ofString p.1, shapeToHOL p.2))
    name context.structs hn (fun p hp => (hc p hp).1)
  cases hinfo : lookupInfo name context.structs with
  | none =>
      simp [structPassContextToExact, structContextToCompileShapeExact,
        hlookup, hinfo, structCompileExp, expToHOL]
  | some info =>
      have hdeclared : ListParamByteRanged info.fields :=
        lookupInfo_payload_invariant (fun info : StructInfo => ListParamByteRanged info.fields)
          name context.structs (fun p hp => (hc p hp).2) info hinfo
      have hkeys := structCompileFields_keys_ranged context fields
        structCompileShape structOldExpShape hf
      have hselected := encodedStructSelectFields info.fields
        (structCompileExp.structCompileFields context fields) hdeclared hkeys
      simp only [structPassContextToExact, structContextToCompileShapeExact,
        hlookup, hinfo, Option.map_some, structCompileExp.eq_3, expToHOL.eq_3]
      exact congrArg (ExpHOL.rstruct : List (ExpHOL width) → ExpHOL width) hselected

/-- Flapjack shape codec fact used by the Load expression case. -/
theorem compileShapeExact_encode (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    Pancake.PanStructs.CompileShapeExact.compileShapeExact
        (structContextToCompileShapeExact context) (shapeToHOL shape) =
      shapeToHOL (structCompileShape context shape) := by
  have h := congrArg shapeToHOL (structCompileShapeWF_eq_compileShapeExact context shape hc hs)
  simpa only [shapeToHOL_shapeOfHOL, structCompileShape] using h.symm

/-- Flapjack full expression codec correspondence. The premises are exactly
the actual input context/name/shape invariants; no compiled result, successful
evaluation, or pass simulation is assumed. -/
theorem compileExpExact_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expression : Exp (BitVec width)) :
    ExpByteRanged expression →
    Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL expression) =
      expToHOL (structCompileExp context expression) := by
  refine Exp.rec (α := BitVec width)
    (motive_1 := fun e => ExpByteRanged e →
      Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL e) =
        expToHOL (structCompileExp context e))
    (motive_2 := fun es => ListExpByteRanged es →
      Pancake.PanStructs.CompileShapeExact.compileExpsExact
        (structPassContextToExact context) (es.map expToHOL) =
        (structCompileExp.structCompileExps context es).map expToHOL)
    (motive_3 := fun fs => ListFieldByteRanged fs →
      Pancake.PanStructs.CompileShapeExact.compileFieldsExact
        (structPassContextToExact context) (fs.map fun p => (ofString p.1, expToHOL p.2)) =
        (structCompileExp.structCompileFields context fs).map
          (fun p => (ofString p.1, expToHOL p.2)))
    (motive_4 := fun p => ExpByteRanged p.2 →
      Pancake.PanStructs.CompileShapeExact.compileExpExact
        (structPassContextToExact context) (expToHOL p.2) =
        expToHOL (structCompileExp context p.2))
    (fun _ _ => by simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact])
    (fun _ _ _ => by simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
      structCompileExp])
    (fun fields ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun index value ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun name fields ih he => by
      exact compileExpExact_nStruct_encode context name fields hc he.1 he.2 (ih he.2))
    (fun field value ih he => by
      exact compileExpExact_nField_encode context field value hc hl hg he.1 he.2 (ih he.2))
    (fun shape address ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, structPassContextToExact,
        compileShapeExact_encode context.structs shape hc he.1]
      exact ih he.2)
    (fun address ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun address ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun operator args ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun operator args ih he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ih he])
    (fun operator left right ihl ihr he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ihl he.1, ihr he.2])
    (fun operator left right ihl ihr he => by
      simp only [ExpByteRanged] at he
      simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
        structCompileExp, ihl he.1, ihr he.2])
    (fun _ => by simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
      structCompileExp])
    (fun _ => by simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
      structCompileExp])
    (fun _ => by simp [expToHOL, Pancake.PanStructs.CompileShapeExact.compileExpExact,
      structCompileExp])
    (fun _ => by simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact,
      structCompileExp.structCompileExps])
    (fun head tail ihhead ihtail he => by
      simp only [ListExpByteRanged] at he
      simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact,
        structCompileExp.structCompileExps, ihhead he.1, ihtail he.2])
    (fun _ => by simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact,
      structCompileExp.structCompileFields])
    (fun head tail ihhead ihtail he => by
      simp only [ListFieldByteRanged] at he
      rcases head with ⟨name, value⟩
      simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact,
        structCompileExp.structCompileFields, ihhead he.2.1, ihtail he.2.2])
    (fun name value ih => ih)
    expression

/-- Flapjack public list codec correspondence, with actual input ranges. -/
theorem compileExpsExact_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expressions : List (Exp (BitVec width))) (he : ListExpByteRanged expressions) :
    Pancake.PanStructs.CompileShapeExact.compileExpsExact
      (structPassContextToExact context) (expressions.map expToHOL) =
      (structCompileExp.structCompileExps context expressions).map expToHOL := by
  induction expressions with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact,
      structCompileExp.structCompileExps]
  | cons expression expressions ih =>
      simp only [ListExpByteRanged] at he
      simp [Pancake.PanStructs.CompileShapeExact.compileExpsExact,
        structCompileExp.structCompileExps,
        compileExpExact_encode context hc hl hg expression he.1, ih he.2]

/-- Flapjack public field codec correspondence preserves keys, duplicates,
order and omissions without assuming anything about compiled outputs. -/
theorem compileFieldsExact_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (fields : List (String × Exp (BitVec width))) (he : ListFieldByteRanged fields) :
    Pancake.PanStructs.CompileShapeExact.compileFieldsExact
      (structPassContextToExact context)
      (fields.map (fun p => (ofString p.1, expToHOL p.2))) =
      (structCompileExp.structCompileFields context fields).map
        (fun p => (ofString p.1, expToHOL p.2)) := by
  induction fields with
  | nil => simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact,
      structCompileExp.structCompileFields]
  | cons field fields ih =>
      rcases field with ⟨name, expression⟩
      simp only [ListFieldByteRanged] at he
      simp [Pancake.PanStructs.CompileShapeExact.compileFieldsExact,
        structCompileExp.structCompileFields,
        compileExpExact_encode context hc hl hg expression he.2.1, ih he.2.2]

/-- Executable codec wrapper around the reviewed exact expression compiler.
The correspondence below licenses its use on parser-ranged production inputs. -/
def structCompileExpExactProduction {width : Nat} [NeZero width]
    (context : StructPassContext) (expression : Exp (BitVec width)) : Exp (BitVec width) :=
  expOfHOL (Pancake.PanStructs.CompileShapeExact.compileExpExact
    (structPassContextToExact context) (expToHOL expression))

/-- Flapjack decoded production equality; the output range premise is proved
by the existing compiler's preservation theorem rather than assumed. -/
theorem structCompileExpExactProduction_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expression : Exp (BitVec width)) (he : ExpByteRanged expression) :
    structCompileExpExactProduction context expression = structCompileExp context expression := by
  unfold structCompileExpExactProduction
  rw [compileExpExact_encode context hc hl hg expression he]
  exact expOfHOL_expToHOL _ (structCompileExp_byteRanged context hc expression he)

end Flapjack
