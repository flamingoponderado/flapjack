import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBlock
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveLists
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveNumeric
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveGlobal
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBytes
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveCopy
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveFfi
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveThunk

/-! Complete generic closure primitive simulation. -/
namespace Flapjack.Compiler.Backend.ClosProps.PrimitiveTotal
open ClosSem Flapjack.SemanticPrimitivesProps
open PrimitiveBoolean PrimitiveBlock PrimitiveLists PrimitiveNumeric PrimitiveGlobal
open PrimitiveBytes PrimitiveMemory PrimitiveAlloc PrimitiveCopy PrimitiveFfi PrimitiveThunk

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- GC configuration case of the reverse primitive simulation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRevConfigGC {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F) (xs ys : List Value)
    (h : simpleValRel vr ∧ simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp (.memOp .configGC) ys t with
    | .err err2 => ∃ err1, doApp (.memOp .configGC) xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp (.memOp .configGC) xs s = .val (x, s1) := by
  obtain ⟨simple, _, states, values⟩ := h
  cases values with
  | nil => simp [doApp, applyMemory, excRel]
  | @cons x1 y1 _ _ first tail =>
    cases tail with
    | nil => simp [doApp, applyMemory, excRel]
    | @cons x2 y2 _ _ second tail =>
      cases tail with
      | cons third rest => simp [doApp, applyMemory, excRel]
      | nil =>
        have firstView := simpleValRel_view vr simple x1 y1 first
        have secondView := simpleValRel_view vr simple x2 y2 second
        have unit : vr unitValue unitValue := (simple.2.1 _ [] _).2 ⟨[], rfl, .nil⟩
        cases firstView <;> cases secondView <;> simp [doApp, applyMemory, excRel, states, unit]

/-- Reverse simulation of every closure primitive operation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app_rev"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoAppRev {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (xs ys : List Value) (op : ClosLang.Op)
    (simple : simpleValRel vr ∧ simpleStateRel vr sr)
    (related : sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp op ys t with
    | .err err2 => ∃ err1, doApp op xs s = .err err1 ∧ excRel vr err1 err2
    | .val (y, t1) => ∃ x s1, vr x y ∧ sr s1 t1 ∧ doApp op xs s = .val (x, s1) := by
  have h := And.intro simple.1 (And.intro simple.2 (And.intro related.1 related.2))
  cases op with
  | label _ | install => simp [doApp, excRel]
  | ffi name => exact simpleValRelDoAppRevFfi name vr sr s t xs ys h
  | intOp op => exact simpleValRelDoAppRevInt vr sr op s t xs ys h
  | wordOp op => exact simpleValRelDoAppRevWord vr sr op s t xs ys h
  | thunkOp op =>
    cases op with
    | forceThunk => simp [doApp, excRel]
    | allocThunk mode => exact simpleValRelDoAppRevAllocThunk mode vr sr s t xs ys h
    | updateThunk mode => exact simpleValRelDoAppRevUpdateThunk mode vr sr s t xs ys h
  | globOp op =>
    cases op with
    | global index => exact simpleValRelDoAppRevGlobal index vr sr s t xs ys h
    | setGlobal index => exact simpleValRelDoAppRevSetGlobal index vr sr s t xs ys h
    | allocGlobal => exact simpleValRelDoAppRevAllocGlobal vr sr s t xs ys h
    | globalsPtr | setGlobalsPtr => simp [doApp, applyGlobal, excRel]
  | blockOp op =>
    cases op with
    | cons tag => exact simpleValRelDoAppRevCons tag vr sr s t xs ys h
    | elemAt index => exact simpleValRelDoAppRevElemAt index vr sr s t xs ys h
    | tagLenEq tag length => exact simpleValRelDoAppRevTagLenEq tag length vr sr s t xs ys h
    | lenEq length => exact simpleValRelDoAppRevLenEq length vr sr s t xs ys h
    | tagEq tag => exact simpleValRelDoAppRevTagEq tag vr sr s t xs ys h
    | lengthBlock => exact simpleValRelDoAppRevLength vr sr s t xs ys h
    | boolTest test => exact simpleValRelDoAppRevBoolTest vr sr test s t xs ys h
    | boolNot => exact simpleValRelDoAppRevBoolNot vr sr s t xs ys h
    | boundsCheckBlock => exact simpleValRelDoAppRevBounds vr sr s t xs ys h
    | consExtend tag => exact simpleValRelDoAppRevConsExtend tag vr sr s t xs ys h
    | fromList tag => exact simpleValRelDoAppRevFromList vr sr tag s t xs ys h
    | listAppend => exact simpleValRelDoAppRevListAppend vr sr s t xs ys h
    | constant constant => exact simpleValRelDoAppRevConstant constant vr sr s t xs ys h
    | equal => exact simpleValRelDoAppRevEqual vr sr s t xs ys h
    | equalConst constant => exact simpleValRelDoAppRevEqualConst constant vr sr s t xs ys h
    | build parts => exact simpleValRelDoAppRevBuild parts vr sr s t xs ys h
  | memOp op =>
    cases op with
    | ref => exact simpleValRelDoAppRevRef vr sr s t xs ys h
    | update => exact simpleValRelDoAppRevUpdateArray vr sr s t xs ys h
    | el => exact simpleValRelDoAppRevEl vr sr s t xs ys h
    | length => exact simpleValRelDoAppRevLengthArray vr sr s t xs ys h
    | lengthByte => exact simpleValRelDoAppRevLengthByte vr sr s t xs ys h
    | refByte flag => exact simpleValRelDoAppRevRefByte flag vr sr s t xs ys h
    | refArray => exact simpleValRelDoAppRevRefArray vr sr s t xs ys h
    | derefByte => exact simpleValRelDoAppRevDerefByte vr sr s t xs ys h
    | updateByte => exact simpleValRelDoAppRevUpdateByte vr sr s t xs ys h
    | concatByteVec => exact simpleValRelDoAppRevConcatByteVec vr sr s t xs ys h
    | copyByte fresh =>
      cases fresh with
      | false => exact simpleValRelDoAppRevCopyByteWrite vr sr s t xs ys h
      | true => exact simpleValRelDoAppRevCopyByteNew vr sr s t xs ys h
    | fromListByte => exact simpleValRelDoAppRevFromListByte vr sr s t xs ys h
    | toListByte => exact simpleValRelDoAppRevToListByte vr sr s t xs ys h
    | lengthByteVec => exact simpleValRelDoAppRevLengthByteVec vr sr s t xs ys h
    | derefByteVec => exact simpleValRelDoAppRevDerefByteVec vr sr s t xs ys h
    | stringCmp fast comparison => exact simpleValRelDoAppRevStringCmp fast comparison vr sr s t xs ys h
    | xorByte => exact simpleValRelDoAppRevXorByte vr sr s t xs ys h
    | boundsCheckArray => exact simpleValRelDoAppRevBoundsCheckArray vr sr s t xs ys h
    | boundsCheckByte loose => exact simpleValRelDoAppRevBoundsCheckByte loose vr sr s t xs ys h
    | mutCons _ _ | updateCons | finaliseCons => simp [doApp, applyMemory, excRel]
    | configGC => exact simpleValRelDoAppRevConfigGC vr sr s t xs ys h

/-- Forward simulation of every closure primitive operation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_do_app"
  (fmap_as_finite_support := [refs, code])]
theorem simpleValRelDoApp {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (xs ys : List Value) (op : ClosLang.Op)
    (simple : simpleValRel vr ∧ simpleStateRel vr sr)
    (related : sr s t ∧ List.Forall₂ vr xs ys) :
    match doApp op xs s with
    | .err err1 => ∃ err2, doApp op ys t = .err err2 ∧ excRel vr err1 err2
    | .val (x, s1) => ∃ y t1, vr x y ∧ sr s1 t1 ∧ doApp op ys t = .val (y, t1) := by
  have reverse := simpleValRelDoAppRev vr sr s t xs ys op simple related
  cases source : doApp op xs s with
  | err err1 =>
    cases target : doApp op ys t with
    | err err2 =>
      simp only [target] at reverse
      obtain ⟨err, eq, rel⟩ := reverse
      rw [source] at eq
      cases eq
      exact ⟨err2, rfl, rel⟩
    | val pair =>
      cases pair with
      | mk value state =>
        simp only [target] at reverse
        obtain ⟨_, _, _, _, eq⟩ := reverse
        rw [source] at eq
        contradiction
  | val pair =>
    cases pair with
    | mk value state =>
      cases target : doApp op ys t with
      | err err2 =>
        simp only [target] at reverse
        obtain ⟨_, eq, _⟩ := reverse
        rw [source] at eq
        contradiction
      | val pair2 =>
        cases pair2 with
        | mk value2 state2 =>
          simp only [target] at reverse
          obtain ⟨v, next, vrRel, srRel, eq⟩ := reverse
          rw [source] at eq
          cases eq
          exact ⟨value2, state2, vrRel, srRel, rfl⟩

end Flapjack.Compiler.Backend.ClosProps.PrimitiveTotal
