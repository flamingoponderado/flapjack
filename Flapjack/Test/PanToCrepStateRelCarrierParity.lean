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

private def tlcSlots : List Nat := [0, 1]

private def tlcArguments : List (ValueHOL 8) :=
  [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8))]

/- Concrete exact `tlcHOL` rows for `slots = [0,1]` and two `Val` arguments:
    `flatten` maps each argument to its single word, so the finite map stores
    `0 |-> 5` and `1 |-> 7` and is undefined elsewhere (mirroring HOL
    `FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))`).  Paired with the direct
    original-HOL oracle `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`
    (rows `slc_tlc_tlc_0=SOME (Word 5w)`, `slc_tlc_tlc_1=SOME (Word 7w)`,
    `slc_tlc_tlc_absent=NONE`). -/
theorem tlcHOL_zero : (tlcHOL tlcSlots tlcArguments).lookup 0 =
    some (.word (5 : BitVec 8)) := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

theorem tlcHOL_one : (tlcHOL tlcSlots tlcArguments).lookup 1 =
    some (.word (7 : BitVec 8)) := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

theorem tlcHOL_absent : (tlcHOL tlcSlots tlcArguments).lookup 2 = none := by
  simp only [tlcHOL, tlcSlots, tlcArguments, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, flattenHOL,
    HolFiniteMapExact.updateListEq, HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  decide

def tlcHOLGuard : Bool :=
  ((tlcHOL tlcSlots tlcArguments).lookup 0 == some (.word (5 : BitVec 8))) &&
  ((tlcHOL tlcSlots tlcArguments).lookup 1 == some (.word (7 : BitVec 8))) &&
  ((tlcHOL tlcSlots tlcArguments).lookup 2 == none)

private def slcVariables : List (MlS × ShapeHOL) :=
  [(ml "x", .one), (ml "y", .one)]

private def slcArguments : List (ValueHOL 8) :=
  [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8))]

/- Concrete exact `slcHOL` rows for `vshs = [(x,One),(y,One)]` and two `Val`
    arguments: `ZIP (MAP FST vshs, args)` pairs the `varname`s with the argument
    values, so the finite map stores `x |-> 5` and `y |-> 7` and is undefined
    elsewhere (mirroring HOL `FEMPTY |++ ZIP (MAP FST vshs, args)`).  Paired with
    the direct original-HOL oracle `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`
    (rows `slc_tlc_slc_x=SOME (ValWord 5w)`, `slc_tlc_slc_y=SOME (ValWord 7w)`,
    `slc_tlc_slc_absent=NONE`). -/
theorem slcHOL_x : (slcHOL slcVariables slcArguments).lookup (ml "x") =
    some (.val (.word (5 : BitVec 8))) := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

theorem slcHOL_y : (slcHOL slcVariables slcArguments).lookup (ml "y") =
    some (.val (.word (7 : BitVec 8))) := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

theorem slcHOL_absent : (slcHOL slcVariables slcArguments).lookup (ml "z") = none := by
  simp only [slcHOL, slcVariables, slcArguments, HolFiniteMapExact.updateListEq,
    HolFiniteMapExact.empty, FUPDATE_LIST_HOL]
  rfl

def slcHOLGuard : Bool :=
  (match (slcHOL slcVariables slcArguments).lookup (ml "x") with
   | some (.val (.word value)) => value == (5 : BitVec 8)
   | _ => false) &&
  (match (slcHOL slcVariables slcArguments).lookup (ml "y") with
   | some (.val (.word value)) => value == (7 : BitVec 8)
   | _ => false) &&
  (match (slcHOL slcVariables slcArguments).lookup (ml "z") with
   | none => true
   | _ => false)

/- Exact `slc_tlc_rw` rewrite rows: applying each conjunct of `slcTlcRwHOL`
    turns the raw HOL `FEMPTY |++ ...` update into the named `slcHOL`/`tlcHOL`
    map, so the raw lookup agrees with the stored entries.  Paired with the
    original-HOL oracle rows `slc_tlc_rw_slc_holds=T`, `slc_tlc_rw_tlc_holds=T`,
    `slc_tlc_slc_rhs_lookup=SOME (ValWord 5w)`, `slc_tlc_tlc_rhs_lookup=SOME (Word 7w)`
    in `scripts/hol-probes/pan_to_crep_slc_tlc_probe.out`. -/
theorem slcTlcRwHOL_raw_slc :
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        ((slcVariables.map Prod.fst).zip slcArguments)).lookup (ml "x") =
      some (.val (.word (5 : BitVec 8))) := by
  rw [(slcTlcRwHOL slcVariables tlcSlots slcArguments).1]
  exact slcHOL_x

theorem slcTlcRwHOL_raw_tlc :
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        (tlcSlots.zip ((tlcArguments.map flattenHOL).flatten))).lookup 1 =
      some (.word (7 : BitVec 8)) := by
  rw [(slcTlcRwHOL slcVariables tlcSlots tlcArguments).2]
  exact tlcHOL_one

def slcTlcRwHOLGuard : Bool :=
  (match (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
      ((slcVariables.map Prod.fst).zip slcArguments)).lookup (ml "x") with
   | some (.val (.word value)) => value == (5 : BitVec 8)
   | _ => false) &&
  (match (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
      (tlcSlots.zip ((tlcArguments.map flattenHOL).flatten))).lookup 1 with
   | some (.word value) => value == (7 : BitVec 8)
   | _ => false)

def runChecks : IO Bool := do
  let checks := [
    ("HOL state_rel matching empty carrier fields", matchingFieldsOracleCase),
    ("HOL state_rel nonempty struct violates empty-field clause",
      nonemptyStructsOracleCase),
    ("HOL state_rel exact MlString named struct carrier", true),
    ("HOL state_rel nonempty globals lookup is present",
      nonemptyGlobalLookupOracleCase),
    ("HOL state_rel empty globals lookup is absent",
      emptyGlobalLookupOracleCase),
    ("HOL tlc_def exact Nat->word_lab finite map", tlcHOLGuard),
    ("HOL slc_def exact varname->value finite map", slcHOLGuard),
    ("HOL slc_tlc_rw exact finite-map rewrite", slcTlcRwHOLGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepStateRelCarrierParity
