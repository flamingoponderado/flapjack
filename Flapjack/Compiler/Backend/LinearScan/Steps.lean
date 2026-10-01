import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.HiddenState
import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Compiler.Backend.RegAlloc.StExMap
import Flapjack.Misc.MiscThe

/-!
# linear_scan colouring steps

Ports of `linear_scanScript.sml:497-705`: releasing inactive intervals,
choosing, stealing and spilling colours, and the two allocation passes'
per-register steps and initial states, over the hidden-state monad of
`HiddenState`. HOL record updates `st with f updated_by g` are Lean structure
updates `{ st with f := g st.f }`; `FILTER ($<> col)` keeps the elements `x`
with `col ≠ x`. Proof-side ports; the executed allocator is unchanged.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- HOL `remove_inactive_intervals` (`linear_scanScript.sml:497-517`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "remove_inactive_intervals_def"]
def removeInactiveIntervals (beg : Int) (st : LinearScanState) : LsM LinearScanState :=
  match _h : st.active with
  | [] => ret st
  | (e, r) :: activetail =>
      if e < beg then
        bind (colorsSub r) fun col =>
          let st' := { st with active := activetail, colorpool := col :: st.colorpool }
          removeInactiveIntervals beg st'
      else ret st
termination_by st.active.length
decreasing_by simp [_h]

/-- HOL `add_active_interval` (`linear_scanScript.sml:519-529`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "add_active_interval_def"]
def addActiveInterval : Int × Nat → List (Int × Nat) → List (Int × Nat)
  | v, [] => [v]
  | v1, v2 :: tail =>
      if v1.1 ≤ v2.1 then v1 :: v2 :: tail
      else v2 :: addActiveInterval v1 tail

/-- HOL `find_color_in_list` (`linear_scanScript.sml:531-543`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_color_in_list_def"]
def findColorInList : List Nat → NumSet → Option (Nat × List Nat)
  | [], _ => none
  | r :: rs, forbidden =>
      if sptLookup r forbidden = none then some (r, rs)
      else
        match findColorInList rs forbidden with
        | none => none
        | some (col, rest) => some (col, r :: rest)

/-- HOL `find_color_in_colornum` (`linear_scanScript.sml:545-551`); the
forbidden set is not consulted, as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "find_color_in_colornum_def"]
def findColorInColornum (st : LinearScanState) (_forbidden : NumSet) :
    LinearScanState × Option Nat :=
  if st.colormax ≤ st.colornum then (st, none)
  else ({ st with colornum := st.colornum + 1 }, some st.colornum)

/-- HOL `find_color` (`linear_scanScript.sml:553-558`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_color_def"]
def findColor (st : LinearScanState) (forbidden : NumSet) : LinearScanState × Option Nat :=
  match findColorInList st.colorpool forbidden with
  | some (col, rest) => ({ st with colorpool := rest }, some col)
  | none => findColorInColornum st forbidden

/-- HOL `spill_register` (`linear_scanScript.sml:560-566`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "spill_register_def"]
def spillRegister (st : LinearScanState) (reg : Nat) : LsM LinearScanState :=
  ignoreBind (updateColors reg st.stacknum) (ret { st with stacknum := st.stacknum + 1 })

/-- HOL `color_register` (`linear_scanScript.sml:568-582`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "color_register_def"]
def colorRegister (st : LinearScanState) (reg col : Nat) (rend : Int) : LsM LinearScanState :=
  ignoreBind (updateColors reg col)
    (if isPhyVar reg then
      ret { st with active := addActiveInterval (rend, reg) st.active,
                    phyregs := sptInsert col () st.phyregs }
    else ret { st with active := addActiveInterval (rend, reg) st.active })

/-- HOL `find_last_stealable` (`linear_scanScript.sml:584-605`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_last_stealable_def"]
def findLastStealable : List (Int × Nat) → NumSet →
    LsM (Option ((Int × Nat) × List (Int × Nat)))
  | [], _ => ret none
  | x :: xs, forbidden =>
      bind (findLastStealable xs forbidden) fun recursion =>
        match recursion with
        | some (steal, rest) => ret (some (steal, x :: rest))
        | none =>
            bind (colorsSub x.2) fun xcol =>
              if ¬ isPhyVar x.2 ∧ sptLookup xcol forbidden = none then ret (some (x, xs))
              else ret none

/-- HOL `find_spill` (`linear_scanScript.sml:607-623`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_spill_def"]
def findSpill (st : LinearScanState) (forbidden : NumSet) (reg : Nat) (rend : Int)
    (force : Bool) : LsM LinearScanState :=
  bind (findLastStealable st.active forbidden) fun stealable =>
    match stealable with
    | none => spillRegister st reg
    | some ((stealend, stealreg), newactive) =>
        if force ∨ rend < stealend then
          bind (colorsSub stealreg) fun stealcolor =>
            bind (spillRegister { st with active := newactive } stealreg) fun st' =>
              colorRegister st' reg stealcolor rend
        else spillRegister st reg

/-- HOL `linear_reg_alloc_step_aux` (`linear_scanScript.sml:625-636`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_step_aux_def"]
def linearRegAllocStepAux (st : LinearScanState) (forbidden : NumSet) (preferred : List Nat)
    (reg : Nat) (rend : Int) (force : Bool) : LsM LinearScanState :=
  let preferred_filtered := preferred.filter (fun c => decide (c ∈ st.colorpool))
  match findColorInList preferred_filtered forbidden with
  | some (col, _) =>
      colorRegister { st with colorpool := st.colorpool.filter (fun x => decide (col ≠ x)) }
        reg col rend
  | none =>
      match findColor st forbidden with
      | (st', some col) => colorRegister st' reg col rend
      | (st', none) => findSpill st' forbidden reg rend force

/-- HOL `linear_reg_alloc_step_pass1` (`linear_scanScript.sml:638-663`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_step_pass1_def"]
def linearRegAllocStepPass1 (forced moves : Spt (List Nat)) (st : LinearScanState) (reg : Nat) :
    LsM LinearScanState :=
  bind (intBegSub reg) fun rbeg =>
    bind (intEndSub reg) fun rend =>
      bind (removeInactiveIntervals rbeg st) fun st' =>
        if isStackVar reg then spillRegister st' reg
        else
          bind (stExMap colorsSub (miscThe [] (sptLookup reg forced))) fun forced_forbidden_list =>
            let forced_forbidden := sptFromAList (forced_forbidden_list.map (fun c => (c, ())))
            if isPhyVar reg then
              if reg < 2 * st'.colormax then
                let forbidden := sptUnion st'.phyregs forced_forbidden
                linearRegAllocStepAux st' forbidden [] reg rend true
              else spillRegister st' reg
            else
              bind (stExMap colorsSub (miscThe [] (sptLookup reg moves))) fun moves_preferred =>
                linearRegAllocStepAux st' forced_forbidden moves_preferred reg rend false

/-- HOL `linear_reg_alloc_step_pass2` (`linear_scanScript.sml:665-682`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_step_pass2_def"]
def linearRegAllocStepPass2 (forced moves : Spt (List Nat)) (st : LinearScanState) (reg : Nat) :
    LsM LinearScanState :=
  bind (intBegSub reg) fun rbeg =>
    bind (intEndSub reg) fun rend =>
      bind (removeInactiveIntervals rbeg st) fun st' =>
        bind (stExMap colorsSub (miscThe [] (sptLookup reg forced))) fun forced_forbidden_list =>
          bind (ret (sptFromAList (forced_forbidden_list.map (fun c => (c, ()))))) fun forced_forbidden =>
            bind (stExMap colorsSub (miscThe [] (sptLookup reg moves))) fun moves_preferred =>
              if isPhyVar reg then
                let forbidden := sptUnion st'.phyregs forced_forbidden
                linearRegAllocStepAux st' forbidden [] reg rend false
              else linearRegAllocStepAux st' forced_forbidden moves_preferred reg rend false

/-- HOL `linear_reg_alloc_pass1_initial_state` (`linear_scanScript.sml:685-694`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_pass1_initial_state_def"]
def linearRegAllocPass1InitialState (k : Nat) : LinearScanState :=
  { active := [], colorpool := [], colornum := 0, colormax := k, phyregs := .ln, stacknum := k }

/-- HOL `linear_reg_alloc_pass2_initial_state` (`linear_scanScript.sml:696-705`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_pass2_initial_state_def"]
def linearRegAllocPass2InitialState (k nreg : Nat) : LinearScanState :=
  { active := [], colorpool := [], colornum := k, colormax := k + nreg, phyregs := .ln,
    stacknum := k + nreg }

end Flapjack.LinearScan
