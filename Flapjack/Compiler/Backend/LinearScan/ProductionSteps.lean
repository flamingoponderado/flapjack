import Flapjack.Compiler.Backend.LinearScan.ProductionSorting
import Flapjack.Compiler.Backend.LinearScan.Steps

/-!
Array-backed coloring and spilling operations. Their simulations are
Flapjack-specific infrastructure; the compiler still uses the source-shaped
list implementation until the entire allocator is verified and connected.
-/
namespace Flapjack.LinearScan.Production

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

def removeInactiveIntervals (beg : Int) (st : LinearScanState) : FastM LinearScanState :=
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

theorem removeInactiveIntervals_correct (beg : Int) (st : LinearScanState) :
    Simulates (removeInactiveIntervals beg st) (LinearScan.removeInactiveIntervals beg st) := by
  rw [removeInactiveIntervals, LinearScan.removeInactiveIntervals]
  cases heq : st.active with
  | nil => simpa only [heq] using simulates_ret st
  | cons head tail =>
    rcases head with ⟨e, r⟩
    by_cases h : e < beg
    · simp only [if_pos h]
      apply simulates_bind _ _ _ _ (colorsSub_correct r)
      intro col
      exact removeInactiveIntervals_correct beg { st with active := tail, colorpool := col :: st.colorpool }
    · simp only [if_neg h]
      exact simulates_ret st
termination_by st.active.length
decreasing_by simp [heq]

def spillRegister (st : LinearScanState) (reg : Nat) : FastM LinearScanState :=
  ignoreBind (updateColors reg st.stacknum) (ret { st with stacknum := st.stacknum + 1 })

theorem spillRegister_correct (st : LinearScanState) (reg : Nat) :
    Simulates (spillRegister st reg) (LinearScan.spillRegister st reg) := by
  simp only [spillRegister, LinearScan.spillRegister]
  exact simulates_ignoreBind _ _ _ _ (updateColors_correct reg st.stacknum) (simulates_ret _)

def colorRegister (st : LinearScanState) (reg col : Nat) (rend : Int) : FastM LinearScanState :=
  ignoreBind (updateColors reg col)
    (if isPhyVar reg then
      ret { st with active := addActiveInterval (rend, reg) st.active,
                    phyregs := sptInsert col () st.phyregs }
    else ret { st with active := addActiveInterval (rend, reg) st.active })

theorem colorRegister_correct (st : LinearScanState) (reg col : Nat) (rend : Int) :
    Simulates (colorRegister st reg col rend) (LinearScan.colorRegister st reg col rend) := by
  simp only [colorRegister, LinearScan.colorRegister]
  apply simulates_ignoreBind _ _ _ _ (updateColors_correct reg col)
  split <;> exact simulates_ret _

def findLastStealable {α : Type} : List (α × Nat) → NumSet →
    FastM (Option ((α × Nat) × List (α × Nat)))
  | [], _ => ret none
  | x :: xs, forbidden =>
      bind (findLastStealable xs forbidden) fun recursion =>
        match recursion with
        | some (steal, rest) => ret (some (steal, x :: rest))
        | none =>
            bind (colorsSub x.2) fun xcol =>
              if ¬ isPhyVar x.2 ∧ sptLookup xcol forbidden = none then ret (some (x, xs))
              else ret none

theorem findLastStealable_correct {α : Type} (xs : List (α × Nat)) (forbidden : NumSet) :
    Simulates (findLastStealable xs forbidden) (LinearScan.findLastStealable xs forbidden) := by
  induction xs with
  | nil => exact simulates_ret none
  | cons x xs ih =>
    simp only [findLastStealable, LinearScan.findLastStealable]
    apply simulates_bind _ _ _ _ ih
    intro recursion
    cases recursion with
    | none =>
      apply simulates_bind _ _ _ _ (colorsSub_correct x.2)
      intro col
      split <;> exact simulates_ret _
    | some result =>
      rcases result with ⟨steal, rest⟩
      exact simulates_ret _

def findSpill (st : LinearScanState) (forbidden : NumSet) (reg : Nat) (rend : Int)
    (force : Bool) : FastM LinearScanState :=
  bind (findLastStealable st.active forbidden) fun stealable =>
    match stealable with
    | none => spillRegister st reg
    | some ((stealend, stealreg), newactive) =>
        if force ∨ rend < stealend then
          bind (colorsSub stealreg) fun stealcolor =>
            bind (spillRegister { st with active := newactive } stealreg) fun st' =>
              colorRegister st' reg stealcolor rend
        else spillRegister st reg

theorem findSpill_correct (st : LinearScanState) (forbidden : NumSet)
    (reg : Nat) (rend : Int) (force : Bool) :
    Simulates (findSpill st forbidden reg rend force)
      (LinearScan.findSpill st forbidden reg rend force) := by
  simp only [findSpill, LinearScan.findSpill]
  apply simulates_bind _ _ _ _ (findLastStealable_correct st.active forbidden)
  intro stealable
  cases stealable with
  | none => exact spillRegister_correct st reg
  | some data =>
    rcases data with ⟨⟨stealend, stealreg⟩, newactive⟩
    by_cases h : force ∨ rend < stealend
    · simp only [if_pos h]
      apply simulates_bind _ _ _ _ (colorsSub_correct stealreg)
      intro color
      apply simulates_bind _ _ _ _ (spillRegister_correct { st with active := newactive } stealreg)
      intro next
      exact colorRegister_correct next reg color rend
    · simpa only [if_neg h] using spillRegister_correct st reg

def linearRegAllocStepAux (st : LinearScanState) (forbidden : NumSet) (preferred : List Nat)
    (reg : Nat) (rend : Int) (force : Bool) : FastM LinearScanState :=
  let preferred_filtered := preferred.filter (fun c => decide (c ∈ st.colorpool))
  match findColorInList preferred_filtered forbidden with
  | some (col, _) =>
      colorRegister { st with colorpool := st.colorpool.filter (fun x => decide (col ≠ x)) }
        reg col rend
  | none =>
      match findColor st forbidden with
      | (st', some col) => colorRegister st' reg col rend
      | (st', none) => findSpill st' forbidden reg rend force

theorem linearRegAllocStepAux_correct (st : LinearScanState) (forbidden : NumSet)
    (preferred : List Nat) (reg : Nat) (rend : Int) (force : Bool) :
    Simulates (linearRegAllocStepAux st forbidden preferred reg rend force)
      (LinearScan.linearRegAllocStepAux st forbidden preferred reg rend force) := by
  simp only [linearRegAllocStepAux, LinearScan.linearRegAllocStepAux]
  cases h : findColorInList (preferred.filter (fun c => decide (c ∈ st.colorpool))) forbidden with
  | some result =>
    rcases result with ⟨col, rest⟩
    exact colorRegister_correct _ reg col rend
  | none =>
    cases h' : findColor st forbidden with
    | mk next col =>
      cases col with
      | none => exact findSpill_correct next forbidden reg rend force
      | some col => exact colorRegister_correct next reg col rend

theorem stExMap_correct {α β : Type} (fast : α → FastM β) (source : α → LsM β)
    (h : ∀ x, Simulates (fast x) (source x)) (xs : List α) :
    Simulates (stExMap fast xs) (stExMap source xs) := by
  induction xs with
  | nil => exact simulates_ret []
  | cons x xs ih =>
    simp only [stExMap]
    apply simulates_bind _ _ _ _ (h x)
    intro y
    apply simulates_bind _ _ _ _ ih
    intro ys
    exact simulates_ret (y :: ys)

def linearRegAllocStepPass1 (forced moves : Spt (List Nat)) (st : LinearScanState) (reg : Nat) :
    FastM LinearScanState :=
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

theorem linearRegAllocStepPass1_correct (forced moves : Spt (List Nat))
    (st : LinearScanState) (reg : Nat) :
    Simulates (linearRegAllocStepPass1 forced moves st reg)
      (LinearScan.linearRegAllocStepPass1 forced moves st reg) := by
  simp only [linearRegAllocStepPass1, LinearScan.linearRegAllocStepPass1]
  apply simulates_bind _ _ _ _ (intBegSub_correct reg)
  intro rbeg
  apply simulates_bind _ _ _ _ (intEndSub_correct reg)
  intro rend
  apply simulates_bind _ _ _ _ (removeInactiveIntervals_correct rbeg st)
  intro next
  by_cases hs : isStackVar reg
  · simp only [if_pos hs]
    exact spillRegister_correct next reg
  · simp only [if_neg hs]
    apply simulates_bind _ _ _ _ (stExMap_correct _ _ colorsSub_correct _)
    intro forbiddenList
    by_cases hp : isPhyVar reg
    · simp only [if_pos hp]
      by_cases hc : reg < 2 * next.colormax
      · simp only [if_pos hc]
        exact linearRegAllocStepAux_correct next _ [] reg rend true
      · simpa only [if_neg hc] using spillRegister_correct next reg
    · simp only [if_neg hp]
      apply simulates_bind _ _ _ _ (stExMap_correct _ _ colorsSub_correct _)
      intro preferred
      exact linearRegAllocStepAux_correct next _ preferred reg rend false

def linearRegAllocStepPass2 (forced moves : Spt (List Nat)) (st : LinearScanState) (reg : Nat) :
    FastM LinearScanState :=
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

theorem linearRegAllocStepPass2_correct (forced moves : Spt (List Nat))
    (st : LinearScanState) (reg : Nat) :
    Simulates (linearRegAllocStepPass2 forced moves st reg)
      (LinearScan.linearRegAllocStepPass2 forced moves st reg) := by
  simp only [linearRegAllocStepPass2, LinearScan.linearRegAllocStepPass2]
  apply simulates_bind _ _ _ _ (intBegSub_correct reg)
  intro rbeg
  apply simulates_bind _ _ _ _ (intEndSub_correct reg)
  intro rend
  apply simulates_bind _ _ _ _ (removeInactiveIntervals_correct rbeg st)
  intro next
  apply simulates_bind _ _ _ _ (stExMap_correct _ _ colorsSub_correct _)
  intro forbiddenList
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro forbidden
  apply simulates_bind _ _ _ _ (stExMap_correct _ _ colorsSub_correct _)
  intro preferred
  by_cases hp : isPhyVar reg
  · simp only [if_pos hp]
    exact linearRegAllocStepAux_correct next _ [] reg rend false
  · simp only [if_neg hp]
    exact linearRegAllocStepAux_correct next _ preferred reg rend false

end Flapjack.LinearScan.Production
