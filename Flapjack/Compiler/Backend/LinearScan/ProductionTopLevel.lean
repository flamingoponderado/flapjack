import Flapjack.Compiler.Backend.LinearScan.ProductionSteps
import Flapjack.Compiler.Backend.LinearScan.TopLevel

/-!
Array-backed allocator orchestration with a simulation against the
list-backed allocator. This is Flapjack-specific implementation infrastructure.
-/
namespace Flapjack.LinearScan.Production

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

def linearRegAllocIntervals (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (reglist_unsorted : List Nat) : FastM Unit :=
  let lenreg := reglist_unsorted.length
  let lenmoves := moves.length
  let st_init_pass1 := linearRegAllocPass1InitialState k
  ignoreBind (listToSortedRegs reglist_unsorted 0) <|
  ignoreBind (sortRegs 0 lenreg) <|
  bind (sortedRegsToList 0 lenreg) fun reglist =>
  bind (ret (reglist.filter isPhyVar)) fun phyregs =>
  bind (ret (phyregs.filter (fun r => decide (r < 2 * k)))) fun phyphyregs =>
  bind (ret (phyregs.filter (fun r => decide (2 * k ≤ r)))) fun stackphyregs =>
  ignoreBind (listToSortedMoves moves 0) <|
  ignoreBind (sortMoves 0 lenmoves) <|
  bind (sortedMovesToList 0 lenmoves) fun smoves =>
  bind (edgesToAdjlist (smoves.map Prod.snd) .ln) fun moves_adjlist =>
  bind (edgesToAdjlist forced .ln) fun forced_adjlist =>
  bind (stExFoldl (linearRegAllocStepPass1 forced_adjlist moves_adjlist) st_init_pass1 reglist)
    fun _st_end_pass1 =>
  ignoreBind (applyRegExchange phyphyregs) <|
  bind (stExFilterGood (fun r =>
      bind (colorsSub r) fun col => ret (decide (isStackVar r = true ∨ k ≤ col))) reglist)
    fun stacklist =>
  bind (ret (linearRegAllocPass2InitialState k stacklist.length)) fun st_init_pass2 =>
  bind (ret (sptFromAList (stacklist.map (fun r => (r, ()))))) fun stackset =>
  bind (ret (sptMap (List.filter (fun r => decide (sptLookup r stackset ≠ none))) forced_adjlist))
    fun forced_adjlist' =>
  bind (ret (sptMap (List.filter (fun r => decide (sptLookup r stackset ≠ none))) moves_adjlist))
    fun moves_adjlist' =>
  bind (stExFoldl (linearRegAllocStepPass2 forced_adjlist' moves_adjlist') st_init_pass2 stacklist)
    fun _st_end_pass2 =>
  applyRegExchange stackphyregs

theorem linearRegAllocIntervals_correct (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (rs : List Nat) :
    Simulates (linearRegAllocIntervals k forced moves rs) (LinearScan.linearRegAllocIntervals k forced moves rs) := by
  simp only [linearRegAllocIntervals, LinearScan.linearRegAllocIntervals]
  apply simulates_ignoreBind _ _ _ _ (listToSortedRegs_correct rs 0)
  apply simulates_ignoreBind _ _ _ _ (sortRegs_correct 0 rs.length)
  apply simulates_bind _ _ _ _ (sortedRegsToList_correct 0 rs.length)
  intro reglist
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro phyregs
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro phyphyregs
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro stackphyregs
  apply simulates_ignoreBind _ _ _ _ (listToSortedMoves_correct moves 0)
  apply simulates_ignoreBind _ _ _ _ (sortMoves_correct 0 moves.length)
  apply simulates_bind _ _ _ _ (sortedMovesToList_correct 0 moves.length)
  intro smoves
  apply simulates_bind _ _ _ _ (edgesToAdjlist_correct _ .ln)
  intro moves_adjlist
  apply simulates_bind _ _ _ _ (edgesToAdjlist_correct _ .ln)
  intro forced_adjlist
  apply simulates_bind _ _ _ _ (stExFoldl_correct _ _ (linearRegAllocStepPass1_correct forced_adjlist moves_adjlist) _ _)
  intro pass1
  apply simulates_ignoreBind _ _ _ _ (applyRegExchange_correct phyphyregs)
  apply simulates_bind _ _ _ _ (stExFilterGood_correct _ _ (fun r => by
    apply simulates_bind _ _ _ _ (colorsSub_correct r)
    intro col
    exact simulates_ret _) _)
  intro stacklist
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro pass2init
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro stackset
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro forced'
  apply simulates_bind _ _ _ _ (simulates_ret _)
  intro moves'
  apply simulates_bind _ _ _ _ (stExFoldl_correct _ _ (linearRegAllocStepPass2_correct forced' moves') _ _)
  intro pass2
  exact applyRegExchange_correct stackphyregs

def extractColoration (invbij : Spt Nat) : List Nat → Spt Nat → FastM (Spt Nat)
  | [], acc => ret acc
  | r :: rs, acc =>
      bind (colorsSub r) fun col =>
        extractColoration invbij rs (sptInsert (miscThe 0 (sptLookup r invbij)) col acc)

theorem extractColoration_correct (invbij : Spt Nat) (rs : List Nat) (acc : Spt Nat) :
    Simulates (extractColoration invbij rs acc) (LinearScan.extractColoration invbij rs acc) := by
  induction rs generalizing acc with
  | nil => exact simulates_ret acc
  | cons r rs ih =>
    simp only [extractColoration, LinearScan.extractColoration]
    apply simulates_bind _ _ _ _ (colorsSub_correct r)
    intro col
    exact ih _

def linearRegAllocAndExtractColoration (ct : ClashTree) (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (reglist_unsorted : List Nat) (invbij : Spt Nat) :
    FastM (Spt Nat) :=
  ignoreBind (getIntervals ct)
    (ignoreBind (linearRegAllocIntervals k forced moves reglist_unsorted)
      (extractColoration invbij reglist_unsorted .ln))

theorem linearRegAllocAndExtractColoration_correct (ct : ClashTree) (k : Nat)
    (forced : List (Nat × Nat)) (moves : List (Nat × (Nat × Nat)))
    (rs : List Nat) (invbij : Spt Nat) (nmax : Nat) :
    Simulates (linearRegAllocAndExtractColoration ct k forced moves rs invbij)
      (LinearScan.linearRegAllocAndExtractColoration ct k forced moves rs invbij nmax) := by
  simp only [linearRegAllocAndExtractColoration, LinearScan.linearRegAllocAndExtractColoration]
  exact simulates_ignoreBind _ _ _ _ (getIntervals_correct ct)
    (simulates_ignoreBind _ _ _ _ (linearRegAllocIntervals_correct k forced moves rs)
      (extractColoration_correct invbij rs .ln))

def runLinearRegAllocIntervals (ct : ClashTree) (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (rs : List Nat) (invbij : Spt Nat)
    (nmax : Nat) : Exc (Spt Nat) StateException :=
  let initial : ProductionState :=
    ⟨Array.replicate (nmax + 1) 0, Array.replicate (nmax + 1) 1,
      Array.replicate (nmax + 1) 1, Array.replicate (nmax + 1) 0,
      Array.replicate moves.length (0, (0, 0))⟩
  (linearRegAllocAndExtractColoration ct k forced moves rs invbij initial).1

theorem runLinearRegAllocIntervals_correct (ct : ClashTree) (k : Nat)
    (forced : List (Nat × Nat)) (moves : List (Nat × (Nat × Nat)))
    (rs : List Nat) (invbij : Spt Nat) (nmax : Nat) :
    runLinearRegAllocIntervals ct k forced moves rs invbij nmax =
      LinearScan.runLinearRegAllocIntervals ct k forced moves rs invbij nmax := by
  let initial : ProductionState :=
    ⟨Array.replicate (nmax + 1) 0, Array.replicate (nmax + 1) 1,
      Array.replicate (nmax + 1) 1, Array.replicate (nmax + 1) 0,
      Array.replicate moves.length (0, (0, 0))⟩
  have h := linearRegAllocAndExtractColoration_correct ct k forced moves rs invbij nmax initial
  have h' := congrArg Prod.fst h
  simpa [runLinearRegAllocIntervals, LinearScan.runLinearRegAllocIntervals,
    LinearScan.runILinearScanHiddenState, linearRegAllocAndExtractColoration,
    Flapjack.Translator.Monadic.MonadBase.ignoreBind, run, initial, ProductionState.toSource] using h'

def linearScanRegAlloc (k : Nat) (moves : List (Nat × (Nat × Nat))) (ct : ClashTree)
    (forced : List (Nat × Nat)) : Exc (Spt Nat) StateException :=
  let bijstate := findBijectionClashTree findBijectionInit ct
  let ct' := applyBijOnClashTree ct bijstate.bij
  let forced' := forced.map (fun (r1, r2) =>
    (miscThe 0 (sptLookup r1 bijstate.bij), miscThe 0 (sptLookup r2 bijstate.bij)))
  let moves' := moves.map (fun (p, (r1, r2)) =>
    (p, (miscThe 0 (sptLookup r1 bijstate.bij), miscThe 0 (sptLookup r2 bijstate.bij))))
  let rs := (sptToAList bijstate.bij).map Prod.snd
  runLinearRegAllocIntervals ct' k forced' moves' rs bijstate.invbij bijstate.nmax

theorem linearScanRegAlloc_correct (k : Nat) (moves : List (Nat × (Nat × Nat)))
    (ct : ClashTree) (forced : List (Nat × Nat)) :
    linearScanRegAlloc k moves ct forced = LinearScan.linearScanRegAlloc k moves ct forced := by
  simp only [linearScanRegAlloc, LinearScan.linearScanRegAlloc]
  exact runLinearRegAllocIntervals_correct _ _ _ _ _ _ _

/-- Compiled callers importing this module may use arrays while Lean's logical
definition remains the source-shaped list implementation. -/
@[csimp] theorem linearScanRegAlloc_code :
    LinearScan.linearScanRegAlloc = linearScanRegAlloc := by
  funext k moves ct forced
  exact (linearScanRegAlloc_correct k moves ct forced).symm

end Flapjack.LinearScan.Production
