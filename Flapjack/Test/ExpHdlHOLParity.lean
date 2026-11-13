module

public import Flapjack.Pancake.PanToCrep
public import Flapjack.Pancake.PanToCrep.ExpHdlExact

import all Flapjack.Pancake.PanToCrep
import all Flapjack.Pancake.PanToCrep.ExpHdlExact
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Pancake.CrepLang.Prog

@[expose] public section

/-!
# Carrier parity fixtures for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`. Every row is replayed through
the tagged exact finite-map rendering `expHdlExact`
(`PanToCrep/ExpHdlExact.lean`, `(fmap_as_finite_support_parameters := [fm])`)
over `MlString`/`ShapeHOL`/`CrepProgHOL`; the untagged raw-map `expHdlHOL`
helper and its duplicate fixtures were retired in task 156. The duplicate
finite-map behavior (the last binding wins for HOL `FLOOKUP`) is checked in
both `FUPDATE` and `FUPDATE_LIST` form on the exact carrier.

`crepProgToHOL_expHdlFiniteMap` is the kernel bridge from the executed
`String`-keyed `expHdlFiniteMap` to the exact carrier; the `bridge` example
below checks it on a duplicate-bearing map.
-/

namespace Flapjack.Test.ExpHdlHOLParity

open Flapjack

abbrev MlS := Flapjack.Pancake.PanLang.MlS
abbrev ShapeHOL := Flapjack.Pancake.PanLang.ShapeHOL
abbrev P64 := CrepProgHOL 64

def nm (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

def keyX : MlS := nm "x"

def knownFM : FiniteMap MlS (ShapeHOL × List Nat) :=
  fun k => if k = keyX then some (.one, [3, 4]) else none

theorem knownSupport :
    ∃ keys : List MlS, ∀ key, knownFM key ≠ none → key ∈ keys := by
  refine ⟨[keyX], ?_⟩
  intro key hk
  by_cases h : key = keyX <;> simp [knownFM, h] at hk ⊢

/-- The exact finite-map carrier driving the tagged `expHdlExact`, built from
    the same lookup function as the raw `knownFM` with an explicit support. -/
def knownExact : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  ⟨knownFM, knownSupport⟩

/-- HOL `FUPDATE` (`|+`) form of a duplicate update on the exact carrier. -/
def dupUpdateExact : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  (HolFiniteMapExact.empty.updateEq (keyX, (.one, [3, 4]))).updateEq
    (keyX, (.one, [7]))

/-- HOL `FUPDATE_LIST` (`|++`) form of the same duplicate update. -/
def dupListExact : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  HolFiniteMapExact.empty.updateListEq [(keyX, (.one, [3, 4])), (keyX, (.one, [7]))]

/-- Three-word global-load row on the exact carrier. -/
def threeWordExact : HolFiniteMapExact MlS (ShapeHOL × List Nat) :=
  HolFiniteMapExact.empty.updateEq (keyX, (.one, [3, 4, 5]))

def exactMissingRow : Bool :=
  match expHdlExact (width := 64) knownExact (nm "missing") with
  | .skip => true
  | _ => false

def exactKnownRow : Bool :=
  match expHdlExact (width := 64) knownExact keyX with
  | .seq (.assign 3 (.loadGlob a0)) (.seq (.assign 4 (.loadGlob a1)) .skip) =>
      a0.toNat == 0 && a1.toNat == 1
  | _ => false

def exactThreeWordRow : Bool :=
  match expHdlExact (width := 64) threeWordExact keyX with
  | .seq (.assign 3 (.loadGlob a0))
      (.seq (.assign 4 (.loadGlob a1)) (.seq (.assign 5 (.loadGlob a2)) .skip)) =>
      a0.toNat == 0 && a1.toNat == 1 && a2.toNat == 2
  | _ => false

def exactDupRow (fm : HolFiniteMapExact MlS (ShapeHOL × List Nat)) : Bool :=
  match expHdlExact (width := 64) fm keyX with
  | .seq (.assign 7 (.loadGlob a0)) .skip => a0.toNat == 0
  | _ => false

def parityGuard : Bool :=
  exactMissingRow && exactKnownRow && exactThreeWordRow &&
    exactDupRow dupUpdateExact && exactDupRow dupListExact

#eval parityGuard
#guard parityGuard

/-- The tagged exact carrier reproduces the HOL `known` row in the kernel
    (the deleted raw-carrier example's observation, restated on the twin). -/
example :
    expHdlExact (width := 64) knownExact keyX =
      .seq (.assign 3 (.loadGlob (BitVec.ofNat 5 0)))
        (.seq (.assign 4 (.loadGlob (BitVec.ofNat 5 1))) .skip) := by
  simp [expHdlExact, knownExact, knownFM, keyX, nm, crepNestedSeqHOL,
    panMap2, loadGlobalsHOL]

private def dupProductionFM : FiniteMap String (Shape × List Nat) :=
  FUPDATE_LIST FEMPTY [("x", (Shape.one, [3, 4])), ("x", (Shape.one, [7]))]

private theorem dupProductionSupport :
    ∃ keys : List String, ∀ key, dupProductionFM key ≠ none → key ∈ keys := by
  refine ⟨["x"], ?_⟩
  intro key hkey
  simp [dupProductionFM, FUPDATE_LIST, FUPDATE, FEMPTY] at hkey ⊢
  split at hkey <;> simp_all

/-- The kernel bridge reproduces the exact carrier on a duplicate-bearing
    production map, so the executed `expHdlFiniteMap` and the tagged
    `expHdlExact` agree under the codecs. -/
example :
    crepProgToHOL (expHdlFiniteMap (α := BitVec 64) dupProductionFM "x")
      = expHdlExact (width := 64) (finiteMapToHOLExact dupProductionFM dupProductionSupport)
          (Flapjack.Basis.Pure.MlString.ofString "x") :=
  crepProgToHOL_expHdlFiniteMap _ _ _ (by decide)

def runChecks : IO Bool := do
  if parityGuard then
    IO.println
      "PASS exp_hdl (exact carriers) missing, two-word, three-word, and duplicate global-load assignments"
  else
    IO.println "FAIL exp_hdl (exact carriers) parity"
  pure parityGuard

end Flapjack.Test.ExpHdlHOLParity
