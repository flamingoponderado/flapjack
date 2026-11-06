import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect

/-! Lean cases paired with `scripts/hol-probes/pan_structs_value_validity_probe.out`. -/

namespace Flapjack.Test

open Flapjack

private abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

private def pairName : ExactName := .implode [80, 97, 105, 114]
private def outerName : ExactName := .implode [79, 117, 116, 101, 114]
private def prefixName : ExactName := .implode [80, 114, 101, 102, 105, 120, 79, 110, 108, 121]
private def leftName : ExactName := .implode [108, 101, 102, 116]
private def rightName : ExactName := .implode [114, 105, 103, 104, 116]
private def innerName : ExactName := .implode [105, 110, 110, 101, 114]
private def tagName : ExactName := .implode [116, 97, 103]
private def markerName : ExactName := .implode [109, 97, 114, 107, 101, 114]

private def exactNestedContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName,
      { fields := [(leftName, .one), (rightName, .comb [])], size := 2 }),
   (outerName,
      { fields := [(innerName, .named pairName), (tagName, .one)], size := 2 })]

private def exactAppendPrefix : Flapjack.Pancake.PanLang.StructContextExact :=
  [(prefixName, { fields := [(markerName, .one)], size := 1 })]

private def exactNestedValue : ValueHOL 8 :=
  .nStruct outerName
    [(innerName,
      .nStruct pairName
        [(leftName, .val (.word 2)), (rightName, .rStruct [])]),
     (tagName, .val (.word 3))]

-- v_flds_ok_nested_match
#guard valueFldsOkHOLExact exactNestedContext exactNestedValue

/-- Exact `panSem$v` / `mlstring` regression for the named nonempty-prefix HOL
    EVAL row `v_flds_ok_append_nonempty_prefix_named`. -/
example : valueFldsOkHOLExact (exactAppendPrefix ++ exactNestedContext)
    exactNestedValue = true := by
  apply valueFldsOkHOLExact_append exactNestedContext exactAppendPrefix exactNestedValue
  · simp [valueFldsOkHOLExact, valuesFldsOkHOLExact, fieldsFldsOkHOLExact,
      Flapjack.Pancake.PanLang.structContextLookupHOL, shapeOfHOLExact,
      shapeEqHOL, shapeEqHOL.shapeEqListHOL, exactNestedContext,
      exactNestedValue, pairName, outerName, leftName, rightName,
      innerName, tagName]
  · simp [exactAppendPrefix, exactNestedContext, prefixName, pairName, outerName,
      leftName, rightName, innerName, tagName]

/-! ## Exact `is_wf_shape_v` over the exact `ValueHOL`/`StructContextExact`
    carriers (HOL `panProps$is_wf_shape_v`, bead flapjack-pxn.18.5.17.1.3.14). -/

private def wrongName : ExactName := .implode [119, 114, 111, 110, 103]

private def exactPairContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 })]

private def exactMatchingValue : ValueHOL 8 :=
  .nStruct pairName [(leftName, .val (.word 2)), (rightName, .rStruct [])]

private def exactMismatchValue : ValueHOL 8 :=
  .nStruct pairName [(leftName, .val (.word 2)), (wrongName, .rStruct [])]

private def exactFirstMatchContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 }),
   (pairName, { fields := [(wrongName, .one)], size := 1 })]

/-- `is_wf_shape_v_word`. -/
example : isWfShapeValueHOLExact exactPairContext (.val (.word 1) : ValueHOL 8) = true := by
  simp [isWfShapeValueHOLExact, exactPairContext]

/-- `is_wf_shape_v_named_match`. -/
example : isWfShapeValueHOLExact exactPairContext exactMatchingValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
    exactMatchingValue, pairName]

/-- `is_wf_shape_v_named_missing`. -/
example : isWfShapeValueHOLExact ([] : Flapjack.Pancake.PanLang.StructContextExact)
    exactMatchingValue = false := by
  simp [isWfShapeValueHOLExact, Flapjack.Pancake.PanLang.structContextLookupHOL,
    exactMatchingValue, pairName]

/-- `is_wf_shape_v_named_mismatch`: `is_wf_shape_v` ignores field names, so the
    renamed field still counts. -/
example : isWfShapeValueHOLExact exactPairContext exactMismatchValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
    exactMismatchValue, pairName]

/-- `is_wf_shape_v_duplicate_second`: a present key suffices regardless of which
    duplicate entry matches first. -/
example : isWfShapeValueHOLExact exactFirstMatchContext exactMatchingValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactFirstMatchContext,
    exactMatchingValue, pairName]

/-- `is_wf_shape_v_nested_match`. -/
example : isWfShapeValueHOLExact exactNestedContext exactNestedValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactNestedContext,
    exactNestedValue, pairName, outerName, leftName, rightName, innerName, tagName]

/-! ## Exact `pan_primop_is_wf_shape_v` over the exact carriers
    (HOL `panProps$pan_primop_is_wf_shape_v`, bead flapjack-4ac.4.14). -/

/-- The tagged `pan_primop_is_wf_shape_v` applies to any exact `pan_primop`
    result. -/
example (values : List (ValueHOL 8)) (value : ValueHOL 8)
    (h : panPrimopHOLExact PrimOp.addCarry values = some value) :
    isWfShapeValueHOLExact exactPairContext value = true :=
  panPrimopHOLExact_isWfShapeValueHOLExact exactPairContext PrimOp.addCarry values value h

/-- A concrete `AddCarry` triple produces a well-formed exact value. -/
example :
    ∃ value, panPrimopHOLExact PrimOp.addCarry
        [.val (.word (2 : BitVec 8)), .val (.word (3 : BitVec 8)),
         .val (.word (4 : BitVec 8))] = some value ∧
      isWfShapeValueHOLExact exactPairContext value = true := by
  refine ⟨_, rfl, ?_⟩
  exact panPrimopHOLExact_isWfShapeValueHOLExact exactPairContext PrimOp.addCarry
    [.val (.word (2 : BitVec 8)), .val (.word (3 : BitVec 8)),
     .val (.word (4 : BitVec 8))] _ rfl

/-! ## Exact `is_wf_shape_v_nil`/`is_wf_shape_v_drop` over the exact carriers
    (HOL `panProps$is_wf_shape_v_nil`/`is_wf_shape_v_drop`, beads
    flapjack-4ac.4.7/.4.8/.4.9). -/

/-- `is_wf_shape_v_nil_step1`. -/
example : isWfShapeValueHOLExact
    ([] : Flapjack.Pancake.PanLang.StructContextExact)
    (.val (.word 1) : ValueHOL 8) = true := by
  apply isWfShapeValueHOLExact_nil_step1
  refine ⟨rfl, ?_⟩
  simp [shapeOfHOLExact]

/-- `is_wf_shape_v_nil`: the two predicates coincide on the empty context. -/
example : Flapjack.Pancake.PanLang.isWfShapeExactHOL
      ([] : Flapjack.Pancake.PanLang.StructContextExact)
      (shapeOfHOLExact (.val (.word 1) : ValueHOL 8)) =
    isWfShapeValueHOLExact
      ([] : Flapjack.Pancake.PanLang.StructContextExact)
      (.val (.word 1) : ValueHOL 8) :=
  isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl _

/-- `is_wf_shape_v_drop`: a value well-formed after dropping still is. -/
example :
    isWfShapeValueHOLExact exactPairContext
      (.val (.word 1) : ValueHOL 8) = true :=
  isWfShapeValueHOLExact_drop 1 exactPairContext
    (.val (.word 1) : ValueHOL 8) (by simp [isWfShapeValueHOLExact])

/-! ## Exact `mem_load_is_wf_shape_v` over the exact carriers (HOL
    `panProps$mem_load_is_wf_shape_v`, bead flapjack-4ac.4.11). -/

/-- The triple conjunction's first component: a loaded `.one` value is
    well-formed in any context. -/
example (domain : BitVec 8 → Prop) [DecidablePred domain]
    (memory : BitVec 8 → HolWordLab 8)
    (h : memLoadHOLExact Flapjack.Pancake.PanLang.ShapeHOL.one 0 domain memory
        ([] : Flapjack.StructContextHOLM) = some (.val (memory 0))) :
    isWfShapeValueHOLExact
      ([] : Flapjack.StructContextHOLM) (.val (memory 0)) = true :=
  (memLoadHOLExact_isWfShapeValueHOLExact).1
    Flapjack.Pancake.PanLang.ShapeHOL.one 0 domain memory
    ([] : Flapjack.StructContextHOLM)
    (.val (memory 0)) h

/-- `mem_load_some_shape_eq`: a loaded `.one` value has shape `.one`. -/
example (domain : BitVec 8 → Prop) [DecidablePred domain]
    (memory : BitVec 8 → HolWordLab 8)
    (h : memLoadHOLExact Flapjack.Pancake.PanLang.ShapeHOL.one 0 domain memory
        ([] : Flapjack.StructContextHOLM) = some (.val (memory 0))) :
    shapeOfHOLExact (.val (memory 0) : ValueHOL 8) =
      Flapjack.Pancake.PanLang.ShapeHOL.one :=
  memLoadHOLExact_some_shapeOf_eq
    Flapjack.Pancake.PanLang.ShapeHOL.one 0 domain memory
    ([] : Flapjack.StructContextHOLM)
    (.val (memory 0)) h

end Flapjack.Test
