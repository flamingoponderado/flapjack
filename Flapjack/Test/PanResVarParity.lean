module

public import Flapjack.PanValues

@[expose] public section

/-!
# Pancake `res_var` parity

The expected results are from the direct HOL probe in
`scripts/hol-probes/pan_res_var_probe.out`, evaluating `res_var_def` in
`cakeml/pancake/semantics/panSemScript.sml:505-508`.
-/

namespace Flapjack.Test.PanResVarParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/semantics/panSemScript.sml:505-508 (res_var_def)"

def locals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 3) else none

def originalDeleteHit : Option (PanValue Nat) := none
def originalDeleteOther : Option (PanValue Nat) := some (.word 3)
def originalUpdateHit : Option (PanValue Nat) := some (.word 7)

def deleteHit : Option (PanValue Nat) :=
  restorePanValueLocal locals "x" none "x"

def deleteOther : Option (PanValue Nat) :=
  restorePanValueLocal locals "y" none "x"

def updateHit : Option (PanValue Nat) :=
  restorePanValueLocal locals "x" (some (.word 7)) "x"

def isWord (value : Option (PanValue Nat)) (expected : Nat) : Bool :=
  match value with
  | some (.word actual) => actual == expected
  | _ => false

def isNone (value : Option (PanValue Nat)) : Bool :=
  match value with
  | none => true
  | some _ => false

#guard originalProbeSource ==
  "cakeml/pancake/semantics/panSemScript.sml:505-508 (res_var_def)"
#guard isNone deleteHit
#guard isWord deleteOther 3
#guard isWord updateHit 7

/-! `flookup_res_var_some_eq_lookup` (`panPropsScript.sml:220`) and
    `flookup_res_var_diff_eq_org` (`:228`). -/

def lookupSameGuard : Bool := isWord (locals "x") 3
def lookupDiffGuard : Bool := isWord (restorePanValueLocal locals "y" none "x") 3

#guard lookupSameGuard
#guard lookupDiffGuard

/-! `FLOOKUP_pan_res_var_thm` (`panPropsScript.sml:236`). -/

def iteGuard : Bool := isWord (restorePanValueLocal locals "y" none "x") 3

#guard iteGuard

/-! `res_var_commutes'` (`pan_to_crepProofScript.sml:4094`). -/

def commGuard : Bool :=
  isWord (restorePanValueLocal (restorePanValueLocal locals "y" none) "x"
      (some (.word 7)) "x") 7 &&
    isNone (restorePanValueLocal (restorePanValueLocal locals "y" none) "x"
      (some (.word 7)) "y")

#eval commGuard
#guard commGuard

/-! `res_var_commutes_strong` (`crep_inlineProofScript.sml:699`). -/

def commStrongGuard : Bool :=
  isWord (restorePanValueLocal (restorePanValueLocal locals "x" (locals "x")) "x"
      (locals "x") "x") 3

#eval commStrongGuard
#guard commStrongGuard

/-! `res_var_foldl_commutes_strong` (`crep_inlineProofScript.sml:706`) and
    `flookup_res_var_is_mem_zip_eq` (`crep_inlineProofScript.sml:802`). -/

def restoreFold (initial saved : VarName → Option (PanValue Nat))
    (names : List VarName) : VarName → Option (PanValue Nat) :=
  (names.zip (names.map saved)).foldl
    (fun current entry => restorePanValueLocal current entry.1 entry.2) initial

def foldGuard : Bool :=
  isWord (restoreFold locals locals ["x", "y"] "x") 3 &&
    isNone (restoreFold locals locals ["x", "y"] "z")

#eval foldGuard
#guard foldGuard

end Flapjack.Test.PanResVarParity
