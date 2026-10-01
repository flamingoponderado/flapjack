import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Steps
import Flapjack.Compiler.Backend.LinearScan.Sorting
import Flapjack.Misc.Sptree.Map
import Flapjack.Misc.Sptree.Foldi

/-!
# linear_scan top-level allocator

Ports of `linear_scanScript.sml:958-1150`: the two-pass interval allocator,
colouring extraction, the register bijection, the generated runner
`run_i_linear_scan_hidden_state`, and `linear_scan_reg_alloc`. HOL `foldi` is
the tagged generic `sptFoldiGen`, `map` the tagged `sptMap`, `the` the tagged
`miscThe`, `OPTION_MAP` `Option.map`, `MAX` `max` and `REPLICATE`
`List.replicate`. Proof-side ports; the executed allocator is unchanged.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- HOL `linear_reg_alloc_intervals` (`linear_scanScript.sml:958-990`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_intervals_def"]
def linearRegAllocIntervals (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (reglist_unsorted : List Nat) : LsM Unit :=
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

/-- HOL `extract_coloration` (`linear_scanScript.sml:992-1002`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "extract_coloration_def"]
def extractColoration (invbij : Spt Nat) : List Nat → Spt Nat → LsM (Spt Nat)
  | [], acc => ret acc
  | r :: rs, acc =>
      bind (colorsSub r) fun col =>
        extractColoration invbij rs (sptInsert (miscThe 0 (sptLookup r invbij)) col acc)

/-- HOL `bijection_state` (`linear_scanScript.sml:1004-1012`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "bijection_state"]
structure BijectionState where
  bij : Spt Nat
  invbij : Spt Nat
  nmax : Nat
  nstack : Nat
  nalloc : Nat
  deriving Repr, DecidableEq

/-- HOL `find_bijection_init` (`linear_scanScript.sml:1014-1022`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_bijection_init_def"]
def findBijectionInit : BijectionState :=
  { bij := .ln, invbij := .ln, nmax := 0, nstack := 3, nalloc := 1 }

/-- HOL `find_bijection_step` (`linear_scanScript.sml:1024-1048`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "find_bijection_step_def"]
def findBijectionStep (state : BijectionState) (r : Nat) : BijectionState :=
  if sptLookup r state.bij ≠ none then state
  else if isPhyVar r then
    { state with bij := sptInsert r r state.bij, invbij := sptInsert r r state.invbij,
                 nmax := max r state.nmax }
  else if isStackVar r then
    { state with bij := sptInsert r state.nstack state.bij,
                 invbij := sptInsert state.nstack r state.invbij,
                 nmax := max state.nstack state.nmax, nstack := state.nstack + 4 }
  else
    { state with bij := sptInsert r state.nalloc state.bij,
                 invbij := sptInsert state.nalloc r state.invbij,
                 nmax := max state.nalloc state.nmax, nalloc := state.nalloc + 4 }

/-- HOL `find_bijection_clash_tree` (`linear_scanScript.sml:1050-1070`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "find_bijection_clash_tree_def"]
def findBijectionClashTree : BijectionState → ClashTree → BijectionState
  | state, .delta wr rd => wr.foldl findBijectionStep (rd.foldl findBijectionStep state)
  | state, .set cutset => sptFoldiGen (fun r _v acc => findBijectionStep acc r) 0 state cutset
  | state, .branch optcutset ct1 ct2 =>
      let state1 := findBijectionClashTree state ct1
      let state2 := findBijectionClashTree state1 ct2
      match optcutset with
      | none => state2
      | some cutset => sptFoldiGen (fun r _v acc => findBijectionStep acc r) 0 state2 cutset
  | state, .seq ct1 ct2 =>
      let state1 := findBijectionClashTree state ct1
      findBijectionClashTree state1 ct2

/-- HOL `apply_bijection` (`linear_scanScript.sml:1072-1075`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "apply_bijection_def"]
def applyBijection (bij : Spt Nat) (interval : Spt Int) : Spt Int :=
  sptFoldiGen (fun r i acc => sptInsert (miscThe 0 (sptLookup r bij)) i acc) 0 .ln interval

/-- The literal carrier generated by `define_run` for `linear_scan_hidden_state`
(`linear_scanScript.sml:1078-1081`, `ml_monadBaseLib.sml:467-527`): each of the
five array fields becomes a `(length, initial element)` pair, in field order,
matching the original `i_linear_scan_hidden_state_CASE` type
`num # num -> num # int -> num # int -> num # num -> num # num # num # num`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "i_linear_scan_hidden_state"]
structure ILinearScanHiddenState where
  colors : Nat × Nat
  int_beg : Nat × Int
  int_end : Nat × Int
  sorted_regs : Nat × Nat
  sorted_moves : Nat × (Nat × (Nat × Nat))
  deriving Repr, DecidableEq

/-- HOL `run_i_linear_scan_hidden_state` generated by `define_run`
(`linear_scanScript.sml:1078-1081`, `ml_monadBaseLib.sml:467-527`): run the
computation on the state whose arrays are `REPLICATE (FST f) (SND f)`. As in
HOL, the computation's result and exception carriers are arbitrary. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "run_i_linear_scan_hidden_state_def"]
def runILinearScanHiddenState {value exception : Type}
    (x : M LinearScanHiddenState value exception) (state : ILinearScanHiddenState) :
    Exc value exception :=
  run x { colors := List.replicate state.colors.1 state.colors.2,
          int_beg := List.replicate state.int_beg.1 state.int_beg.2,
          int_end := List.replicate state.int_end.1 state.int_end.2,
          sorted_regs := List.replicate state.sorted_regs.1 state.sorted_regs.2,
          sorted_moves := List.replicate state.sorted_moves.1 state.sorted_moves.2 }

/-- HOL `linear_reg_alloc_and_extract_coloration` (`linear_scanScript.sml:1083-1090`);
`nmax` is unused, so, as in HOL (`... -> α -> ...`), its type is an
arbitrary independent carrier; callers pass a `Nat`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "linear_reg_alloc_and_extract_coloration_def"]
def linearRegAllocAndExtractColoration {Unused : Type} (ct : ClashTree) (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (reglist_unsorted : List Nat) (invbij : Spt Nat)
    (_nmax : Unused) : LsM (Spt Nat) :=
  ignoreBind (getIntervalsCtMonad ct)
    (ignoreBind (linearRegAllocIntervals k forced moves reglist_unsorted)
      (extractColoration invbij reglist_unsorted .ln))

/-- HOL `size_of_clash_tree` (`linear_scanScript.sml:1092-1106`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "size_of_clash_tree_def"]
def sizeOfClashTree : ClashTree → Int
  | .delta _ _ => 2
  | .set _ => 1
  | .branch optcutset ct1 ct2 =>
      (if optcutset.isSome then 1 else 0) + sizeOfClashTree ct1 + sizeOfClashTree ct2
  | .seq ct1 ct2 => sizeOfClashTree ct1 + sizeOfClashTree ct2

/-- HOL `run_linear_reg_alloc_intervals` (`linear_scanScript.sml:1108-1118`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "run_linear_reg_alloc_intervals_def"]
def runLinearRegAllocIntervals (ct : ClashTree) (k : Nat) (forced : List (Nat × Nat))
    (moves : List (Nat × (Nat × Nat))) (reglist_unsorted : List Nat) (invbij : Spt Nat)
    (nmax : Nat) : Exc (Spt Nat) StateException :=
  runILinearScanHiddenState
    (linearRegAllocAndExtractColoration ct k forced moves reglist_unsorted invbij nmax)
    { colors := (nmax + 1, 0), int_beg := (nmax + 1, 1), int_end := (nmax + 1, 1),
      sorted_regs := (nmax + 1, 0), sorted_moves := (moves.length, (0, (0, 0))) }

/-- HOL `apply_bij_on_clash_tree` (`linear_scanScript.sml:1120-1134`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "apply_bij_on_clash_tree_def"]
def applyBijOnClashTree : ClashTree → Spt Nat → ClashTree
  | .delta wr rd, bij =>
      .delta (wr.map (fun r => miscThe 0 (sptLookup r bij)))
        (rd.map (fun r => miscThe 0 (sptLookup r bij)))
  | .set cutset, bij =>
      .set (sptFoldiGen (fun r _ acc => sptInsert (miscThe 0 (sptLookup r bij)) () acc) 0 .ln cutset)
  | .branch optcutset ct1 ct2, bij =>
      .branch (optcutset.map
          (sptFoldiGen (fun r _ acc => sptInsert (miscThe 0 (sptLookup r bij)) () acc) 0 .ln))
        (applyBijOnClashTree ct1 bij) (applyBijOnClashTree ct2 bij)
  | .seq ct1 ct2, bij => .seq (applyBijOnClashTree ct1 bij) (applyBijOnClashTree ct2 bij)

/-- HOL `linear_scan_reg_alloc` (`linear_scanScript.sml:1138-1146`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_reg_alloc_def"]
def linearScanRegAlloc (k : Nat) (moves : List (Nat × (Nat × Nat))) (ct : ClashTree)
    (forced : List (Nat × Nat)) : Exc (Spt Nat) StateException :=
  let bijstate := findBijectionClashTree findBijectionInit ct
  let ct' := applyBijOnClashTree ct bijstate.bij
  let forced' := forced.map (fun (r1, r2) =>
    (miscThe 0 (sptLookup r1 bijstate.bij), miscThe 0 (sptLookup r2 bijstate.bij)))
  let moves' := moves.map (fun (p, (r1, r2)) =>
    (p, (miscThe 0 (sptLookup r1 bijstate.bij), miscThe 0 (sptLookup r2 bijstate.bij))))
  let reglist_unsorted := (sptToAList bijstate.bij).map Prod.snd
  runLinearRegAllocIntervals ct' k forced' moves' reglist_unsorted bijstate.invbij bijstate.nmax

end Flapjack.LinearScan
