module

public import Flapjack.Pancake.Semantics.PanProps
public import Flapjack.Test.Fixtures.PanProps

-- Checks below run compiled code from these modules.
public meta import Flapjack.Test.Fixtures.PanProps
@[expose] public section

/-! Exact-carrier parity for HOL `panProps$is_wf_shape_of_v`
(`panPropsScript.sml:38`, bead flapjack-4ac.4.6). -/

namespace Flapjack.Test

open Flapjack
open Flapjack.Test.Fixtures.PanProps

private def exactWordValue : ValueHOL 8 := .val (.word 1)

/-- Premise of the port at a `Val`: `is_wf_shape_v` holds trivially. -/
example : isWfShapeValueHOLExact exactPairContext exactWordValue = true := by
  simp [isWfShapeValueHOLExact, exactWordValue]

/-- `is_wf_shape_of_v` at a `Val`: `shape_of (Val w) = One`, which is well-formed. -/
example :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL exactPairContext
      (shapeOfHOLExact exactWordValue) = true :=
  isWfShapeValueHOLExact_shapeOfHOLExact exactPairContext exactWordValue
    (by simp [isWfShapeValueHOLExact, exactWordValue])

/-- Premise of the port at a matching named struct. -/
example : isWfShapeValueHOLExact exactPairContext exactMatchingValue = true :=
  isWfShapeValueHOLExact_matching

/-- `is_wf_shape_of_v` at a matching named struct. -/
example :
    Flapjack.Pancake.PanLang.isWfShapeExactHOL exactPairContext
      (shapeOfHOLExact exactMatchingValue) = true :=
  isWfShapeValueHOLExact_shapeOfHOLExact exactPairContext exactMatchingValue
    (by
      simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
        Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
        exactMatchingValue, pairName])

end Flapjack.Test
