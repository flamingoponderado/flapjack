module

public import Flapjack.Pancake.Semantics.PanProps

@[expose] public section

/-!
# Shared `panProps` oracle fixtures

The named pair context, matching value and the `is_wf_shape_v` row shared by
`Flapjack/Test/PanPropsShapeOfWfParity.lean` and
`Flapjack/Test/PanStructsValueValidityParity.lean`. The names are the HOL
`mlstring`s `Pair`, `left` and `right`; the value is a matching `nStruct`.
-/

namespace Flapjack.Test.Fixtures.PanProps

open Flapjack

abbrev ExactName := Flapjack.Basis.Pure.MlString.MlString

def pairName : ExactName := .implode [80, 97, 105, 114]
def leftName : ExactName := .implode [108, 101, 102, 116]
def rightName : ExactName := .implode [114, 105, 103, 104, 116]

def exactPairContext : Flapjack.Pancake.PanLang.StructContextExact :=
  [(pairName, { fields := [(leftName, .one), (rightName, .comb [])], size := 2 })]

def exactMatchingValue : ValueHOL 8 :=
  .nStruct pairName [(leftName, .val (.word 2)), (rightName, .rStruct [])]

/-- `is_wf_shape_v_named_match`: a matching named struct is well-formed. -/
theorem isWfShapeValueHOLExact_matching :
    isWfShapeValueHOLExact exactPairContext exactMatchingValue = true := by
  simp [isWfShapeValueHOLExact, isWfShapeValuesHOLExact,
    Flapjack.Pancake.PanLang.structContextLookupHOL, exactPairContext,
    exactMatchingValue, pairName]

end Flapjack.Test.Fixtures.PanProps
