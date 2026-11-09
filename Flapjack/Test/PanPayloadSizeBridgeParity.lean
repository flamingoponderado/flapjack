import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiCore

/-!
Regression guards for the #1250 (a) payload-size fix.

HOL bounds returned and raised payloads by
`size_of_sh_with_ctxt s.structs (shape_of value) <= 32`
(`panSemScript.sml:638-652`, `panLangScript.sml:164-172`).  The clocked
evaluator's `panValuePayloadWithinLimit` now uses the structural
`panValuePayloadSize`, which agrees with that shape-based size
(`panValuePayloadSize_eq_sizeOfShWithCtxt`).  The former fuel-indexed size
charged two units per `RStruct` nesting level while `panValueFlatValueFuel`
counts one per node, so deeply nested records were under-counted and the check
accepted payloads HOL rejects.

The guards below pin the smallest former counterexample (a two-deep nested
record of one word) and the decision boundary for a three-deep nested record:
33 words must be rejected, 32 words accepted, and a `Return` of the 33-word
value through the clocked leaf must yield `Error`.

This module is untagged Flapjack infrastructure, not a HOL declaration.
-/

namespace Flapjack.Test.PanPayloadSizeBridgeParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- A three-deep nested `RStruct` whose innermost level holds `count` words:
shape `Comb [Comb [Comb [One × count]]]`, whose HOL size is `count`. -/
private def nestedWords (count : Nat) : PanValue Word64 :=
  .rStruct [.rStruct [.rStruct (List.replicate count (.word (BitVec.ofNat 64 0)))]]

/-- The same three-deep shape as an expression, for the `Return` guard. -/
private def nestedWordsExp (count : Nat) : Exp Word64 :=
  .rStruct [.rStruct [.rStruct (List.replicate count (.const (BitVec.ofNat 64 0)))]]

private def nestedWords32 : PanValue Word64 := nestedWords 32

private def nestedWords33 : PanValue Word64 := nestedWords 33

/-- The smallest former counterexample: a two-deep nested record of one word.
HOL size is 1; the old fuel-indexed size returned 0. -/
private def smallNested : PanValue Word64 :=
  .rStruct [.rStruct [.word (BitVec.ofNat 64 0)]]

#guard panValuePayloadSize [] smallNested == 1
#guard panValuePayloadSize [] nestedWords32 == 32
#guard panValuePayloadSize [] nestedWords33 == 33

#guard panValuePayloadSize [] smallNested ==
  sizeOfShWithCtxt ([] : StructContextHOL) (panValueShape [] smallNested)
#guard panValuePayloadSize [] nestedWords32 ==
  sizeOfShWithCtxt ([] : StructContextHOL) (panValueShape [] nestedWords32)
#guard panValuePayloadSize [] nestedWords33 ==
  sizeOfShWithCtxt ([] : StructContextHOL) (panValueShape [] nestedWords33)

#guard panValuePayloadWithinLimit [] smallNested == true
#guard panValuePayloadWithinLimit [] nestedWords32 == true
#guard panValuePayloadWithinLimit [] nestedWords33 == false

/-- The clocked `Return` leaf on the 33-word nested payload returns `Error`. -/
private def returnIsError : Bool :=
  match panValueReturnResult (structs := ([] : StructContext))
      (baseAddress := (0 : Word64)) (topAddress := (0 : Word64))
      (bytesInWord := (BitVec.ofNat 64 8))
      (locals := fun _ => none) (globals := fun _ => none)
      (memory := fun _ => none) (ffi := statefulTestFfiState)
      (nestedWordsExp 33) (memoryAccess := none) with
  | some (.error _ _ _ _) => true
  | _ => false

/-- The clocked `Return` leaf on the 32-word nested payload returns it. -/
private def returnIsReturned : Bool :=
  match panValueReturnResult (structs := ([] : StructContext))
      (baseAddress := (0 : Word64)) (topAddress := (0 : Word64))
      (bytesInWord := (BitVec.ofNat 64 8))
      (locals := fun _ => none) (globals := fun _ => none)
      (memory := fun _ => none) (ffi := statefulTestFfiState)
      (nestedWordsExp 32) (memoryAccess := none) with
  | some (.returned _ _ _ _ _) => true
  | _ => false

#guard returnIsError
#guard returnIsReturned

def runChecks : IO Bool := do
  let checks : List (String × Bool) := [
    ("two-deep nested size matches HOL shape size",
      panValuePayloadSize [] smallNested ==
        sizeOfShWithCtxt ([] : StructContextHOL) (panValueShape [] smallNested)),
    ("33-word nested payload is rejected",
      panValuePayloadWithinLimit [] nestedWords33 == false),
    ("32-word nested payload is accepted",
      panValuePayloadWithinLimit [] nestedWords32 == true),
    ("Return of the 33-word nested payload yields Error", returnIsError),
    ("Return of the 32-word nested payload yields Return", returnIsReturned)]
  let mut ok := true
  for (name, pass) in checks do
    if pass then IO.println s!"PASS payload-size bridge: {name}"
    else
      IO.println s!"FAIL payload-size bridge: {name}"
      ok := false
  return ok

end Flapjack.Test.PanPayloadSizeBridgeParity
