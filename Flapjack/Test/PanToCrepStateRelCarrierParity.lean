import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.PanSem.ValueHOL
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport

/-!
Direct carrier checks paired with `pan_to_crep_state_rel_carrier_probe.out`.
HOL `state_rel_def` (`pan_to_crepProofScript.sml:45-56`) consumes
`panSem$state.structs : (mlstring # struct_info) list` and requires it empty;
`state_rel_globals` (`:65-68`) requires its `mlstring |-> 'a v` globals map to
be `FEMPTY`. The exact source-side names and struct metadata below use
`MlString`, `ShapeHOL`, and `StructInfoHOLExact`; the value map uses
`HolFiniteMapExact MlString (ValueHOL width)`. These are source-carrier checks,
not an implementation of `state_rel` and not evidence that production
`String`/`Shape` states are exact HOL carriers. The HOL EVAL row for equality
against `FEMPTY` remains an unevaluated function equality; the adjacent
lookup rows pin the nonempty and empty observations without claiming HOL
decides extensional function inequality.
-/

namespace Flapjack.Test.PanToCrepStateRelCarrierParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private abbrev ExactStructContext := List (MlS × StructInfoHOLExact)

private def ml (name : String) : MlS := ofString name

private def exactPairStruct : StructInfoHOLExact :=
  { fields := [(ml "left", .one)], size := 1 }

private def exactNamedStructs : ExactStructContext :=
  [(ml "Pair", exactPairStruct)]

private def exactGlobalMap : HolFiniteMapExact MlS (ValueHOL 8) :=
  (HolFiniteMapExact.empty).update
    (ml "global", ValueHOL.val (.word (3 : BitVec 8)))

private def exactEmptyGlobalMap : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private def exactEmptyStructs : ExactStructContext := []

theorem exact_named_struct_carrier_row :
    exactNamedStructs =
      [(ml "Pair", { fields := [(ml "left", ShapeHOL.one)], size := 1 })] := rfl

theorem exact_nonempty_global_lookup_row :
    exactGlobalMap.lookup (ml "global") =
      some (ValueHOL.val (.word (3 : BitVec 8))) := by
  simp [exactGlobalMap, HolFiniteMapExact.update, FUPDATE]

theorem exact_empty_global_lookup_row :
    exactEmptyGlobalMap.lookup (ml "global") = none := rfl

private def matchingFieldsOracleCase : Bool :=
  exactEmptyStructs.isEmpty && (exactEmptyGlobalMap.lookup (ml "global")).isNone

private def nonemptyStructsOracleCase : Bool :=
  exactNamedStructs.length == 1

private def nonemptyGlobalLookupOracleCase : Bool :=
  match exactGlobalMap.lookup (ml "global") with
  | some (.val (.word value)) => value == (3 : BitVec 8)
  | _ => false

private def emptyGlobalLookupOracleCase : Bool :=
  (exactEmptyGlobalMap.lookup (ml "global")).isNone

/-- Kernel-checked row: the exact `state_rel_structs` projection applies to any
    related exact carrier pair, returning the empty source struct context. -/
example {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.structs = [] :=
  panToCrepStateRelFiniteExact_structs source target hrel

/-- Kernel-checked row: the exact `state_rel_globals` projection applies to any
    related exact carrier pair, returning the pointwise-empty globals map. -/
example {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.globals.lookup = (fun _ => none) :=
  panToCrepStateRelFiniteExact_globals source target hrel

def runChecks : IO Bool := do
  let checks := [
    ("HOL state_rel matching empty carrier fields", matchingFieldsOracleCase),
    ("HOL state_rel nonempty struct violates empty-field clause",
      nonemptyStructsOracleCase),
    ("HOL state_rel exact MlString named struct carrier", true),
    ("HOL state_rel nonempty globals lookup is present",
      nonemptyGlobalLookupOracleCase),
    ("HOL state_rel empty globals lookup is absent",
      emptyGlobalLookupOracleCase)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepStateRelCarrierParity
