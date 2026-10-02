import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.Coalesce
import Flapjack.Compiler.Backend.RegAlloc.Colouring
import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar
import Flapjack.Compiler.Backend.RegAlloc.ExceptionFunctions
import Flapjack.Compiler.Backend.RegAlloc.GraphConstruction
import Flapjack.Compiler.Backend.RegAlloc.Initialization
import Flapjack.Compiler.Backend.RegAlloc.MovePrep
import Flapjack.Compiler.Backend.RegAlloc.MoveTable
import Flapjack.Compiler.Backend.RegAlloc.Remap
import Flapjack.Compiler.Backend.RegAlloc.SafeDiv
import Flapjack.Compiler.Backend.RegAlloc.SortMoves
import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.Compiler.Backend.RegAlloc.SpDefault
import Flapjack.Compiler.Backend.RegAlloc.SpillChoice
import Flapjack.Compiler.Backend.RegAlloc.SplitDegree
import Flapjack.Compiler.Backend.RegAlloc.StateFilter
import Flapjack.Compiler.Backend.RegAlloc.StateForeach
import Flapjack.Compiler.Backend.RegAlloc.StateMap
import Flapjack.Compiler.Backend.RegAlloc.StatePartition
import Flapjack.Compiler.Backend.RegAlloc.StempColouring
import Flapjack.Compiler.Backend.RegAlloc.Worklists
import Flapjack.Misc.LookupAny
import Flapjack.Misc.Sorting

/-!
# reg_alloc: the colouring phases and the top-level allocator

Literal ports of the remaining executable definitions of `reg_allocScript.sml`:
the five `do_step` phases with their helpers `revive_moves`, `unspill` and
`bg_ok` (363-830), the step loop `do_step`/`rpt_do_step` (831-867), the first
allocation pass `init_alloc1_heu`/`do_alloc1` (1250-1296), the move preference
`biased_pref` (1369-1380), and the allocator `do_reg_alloc`, `reg_alloc_aux` and
`reg_alloc` (1449-1493). HOL do-blocks are the accepted MonadBase
`bind`/`ignoreBind`/`ret`; pattern binders are pattern matches; HOL
`PARTITION` is the exact `holPartition`, `EXISTS P l` is `l.any P`, `NULL l`
is `l = []`, `COUNT_LIST d` is `List.range d`, and a HOL `FILTER` predicate is
the corresponding Boolean test. Proof-side ports: the executed allocator is
not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- Literal `revive_moves` (`reg_allocScript.sml:363-377`): unavailable moves
touching a neighbour of `vs` become available again, merged by priority. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "revive_moves_def"]
def reviveMoves (vs : List Nat) : M State Unit StateException :=
  bind (stExMap adjLsSub vs) fun nbs =>
    bind getUnavailMovesWl fun uam =>
      bind getAvailMovesWl fun am =>
        let (rev, unavail) := holPartition
          (fun (m : Nat × (Nat × Nat)) =>
            nbs.any (fun l => sortedMem m.2.1 l) || nbs.any (fun l => sortedMem m.2.2 l)) uam
        let sorted := smerge (sortMoves rev) am
        ignoreBind (setAvailMovesWl sorted) (setUnavailMovesWl unavail)

/-- Literal `unspill` (`reg_allocScript.sml:379-392`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "unspill_def"]
def unspill (k : Nat) : M State Unit StateException :=
  bind getDim fun d =>
    bind getSpillWl fun swl =>
      bind (stExPartition (splitDegree d k) swl [] []) fun (ltk, gtk) =>
        ignoreBind (reviveMoves ltk)
          (bind (stExPartition moveRelatedSub ltk [] []) fun (ltkfreeze, ltksimp) =>
            ignoreBind (setSpillWl gtk)
              (ignoreBind (addSimpWl ltksimp) (addFreezeWl ltkfreeze)))

/-- Literal `do_simplify` (`reg_allocScript.sml:400-415`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_simplify_def"]
def doSimplify (k : Nat) : M State Bool StateException :=
  bind getSimpWl fun simps =>
    if simps = [] then ret false
    else
      ignoreBind (stExForeach simps decDegree)
        (ignoreBind (stExForeach simps pushStack)
          (ignoreBind (setSimpWl [])
            (ignoreBind (unspill k) (ret true))))

/-- Literal `do_coalesce_real` (`reg_allocScript.sml:457-471`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_coalesce_real_def"]
def doCoalesceReal (x y : Nat) (case1 case2 : List Nat) : M State Unit StateException :=
  ignoreBind (updateCoalesced y x)
    (bind (isFixed x) fun bx =>
      ignoreBind (if bx then ret () else incDeg x case2.length)
        (ignoreBind (listInsertEdge x case2)
          (ignoreBind (stExForeach case1 decDeg) (pushStack y))))

/-- Literal `bg_ok` (`reg_allocScript.sml:524-554`): the George criterion, then
the Briggs criterion. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "bg_ok_def"]
def bgOk (k x y : Nat) : M State (Option (List Nat × List Nat)) StateException :=
  bind (adjLsSub x) fun adjx =>
    bind (adjLsSub y) fun adjy =>
      let (case1, case2) := holPartition (fun v => sortedMem v adjx) adjy
      bind (stExFilter (consideredVar k) case1 []) fun case1 =>
        bind (stExFilter (consideredVar k) case2 []) fun case2 =>
          bind (stExMap (degOrInf k) case2) fun case2degs =>
            let c2len := (case2degs.filter (fun x => decide (x ≥ k))).length
            if c2len = 0 then ret (some (case1, case2))
            else
              let case3 := adjx.filter (fun v => !sortedMem v adjy)
              bind (stExFilter (consideredVar k) case3 []) fun case3 =>
                bind (stExMap (degOrInf (k + 1)) case1) fun case1degs =>
                  bind (stExMap (degOrInf k) case3) fun case3degs =>
                    bind (ret (case1degs.filter (fun x => decide (x - 1 ≥ k))).length)
                      fun c1len =>
                        bind (ret (case3degs.filter (fun x => decide (x ≥ k))).length)
                          fun c3len =>
                            if c1len + c2len + c3len < k then ret (some (case1, case2))
                            else ret none

/-- Literal `do_coalesce` (`reg_allocScript.sml:668-690`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_coalesce_def"]
def doCoalesce (k : Nat) : M State Bool StateException :=
  bind getAvailMovesWl fun am =>
    bind (stExFirst consistencyOk (bgOk k) am []) fun (ores, unavail) =>
      ignoreBind (addUnavailMovesWl unavail)
        (match ores with
        | none => ignoreBind (setAvailMovesWl []) (ret false)
        | some ((x, y), (case1, case2), ms) =>
            ignoreBind (setAvailMovesWl ms)
              (ignoreBind (doCoalesceReal x y case1 case2)
                (ignoreBind (unspill k) (ignoreBind (respill k x) (ret true)))))

/-- Literal `do_prefreeze` (`reg_allocScript.sml:726-746`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_prefreeze_def"]
def doPrefreeze (k : Nat) : M State Bool StateException :=
  bind getFreezeWl fun fwl_pre =>
    bind (stExFilter isNotCoalesced fwl_pre []) fun fwl =>
      bind getSpillWl fun swl_pre =>
        bind (stExFilter isNotCoalesced swl_pre []) fun swl =>
          ignoreBind (setSpillWl swl)
            (bind getUnavailMovesWl fun uam_pre =>
              bind (stExFilter (fun (m : Nat × (Nat × Nat)) => consistencyOk m.2.1 m.2.2)
                  uam_pre []) fun uam =>
                ignoreBind (resetMoveRelated uam)
                  (bind (setUnavailMovesWl uam) fun _uam =>
                    bind (stExPartition moveRelatedSub fwl [] []) fun (ltkfreeze, ltksimp) =>
                      ignoreBind (addSimpWl ltksimp)
                        (ignoreBind (setFreezeWl ltkfreeze) (doSimplify k))))

/-- Literal `do_freeze` (`reg_allocScript.sml:750-765`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_freeze_def"]
def doFreeze (k : Nat) : M State Bool StateException :=
  bind getFreezeWl fun freeze =>
    match freeze with
    | [] => ret false
    | x :: xs =>
        ignoreBind (decDegree x)
          (ignoreBind (pushStack x)
            (ignoreBind (setFreezeWl xs) (ignoreBind (unspill k) (ret true))))

/-- Literal `do_spill` (`reg_allocScript.sml:809-829`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_spill_def"]
def doSpill (scostopt : Option (Spt Nat)) (k : Nat) : M State Bool StateException :=
  bind getSpillWl fun spills =>
    bind getDim fun d =>
      match spills with
      | [] => ret false
      | x :: xs =>
          bind (degreesSub x) fun xv =>
            bind (match scostopt with
                | none => stExListMaxDeg xs d x xv []
                | some scost =>
                    stExListMinCost scost xs d x (safeDiv (lookupAny x scost 0) xv) [])
              fun (y, ys) =>
                ignoreBind (decDegree y)
                  (ignoreBind (pushStack y)
                    (ignoreBind (setSpillWl ys) (ignoreBind (unspill k) (ret true))))

/-- Literal `do_step` (`reg_allocScript.sml:831-858`): try simplify, coalesce,
prefreeze, freeze and spill in turn. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_step_def"]
def doStep (scost : Option (Spt Nat)) (k : Nat) : M State Bool StateException :=
  bind (doSimplify k) fun b =>
    if b then ret b
    else
      bind (doCoalesce k) fun b =>
        if b then ret b
        else
          bind (doPrefreeze k) fun b =>
            if b then ret b
            else
              bind (doFreeze k) fun b =>
                if b then ret b
                else bind (doSpill scost k) fun b => ret b

/-- Literal `rpt_do_step` (`reg_allocScript.sml:860-867`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "rpt_do_step_def"]
def rptDoStep (scost : Option (Spt Nat)) (k : Nat) : Nat → M State Unit StateException
  | 0 => ret ()
  | c + 1 => bind (doStep scost k) fun b => if b then rptDoStep scost k c else ret ()

/-- Literal `do_upd_coalesce` (`reg_allocScript.sml:1251-1254`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_upd_coalesce_def"]
def doUpdCoalesce (i : Nat) : M State Unit StateException :=
  updateCoalesced i (0 + i)

/-- Literal `init_alloc1_heu` (`reg_allocScript.sml:1257-1286`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "init_alloc1_heu_def"]
def initAlloc1Heu (moves : List (Nat × (Nat × Nat))) (d k : Nat) :
    M State Nat StateException :=
  bind (ret (List.range d)) fun ds =>
    bind (stExFilter isAtemp ds []) fun allocs =>
      ignoreBind (stExForeach ds (fun i =>
          bind (adjLsSub i) fun adjls =>
            bind (stExFilter (fun v => consideredVar k v) adjls []) fun fills =>
              updateDegrees i fills.length))
        (ignoreBind (stExForeach ds doUpdCoalesce)
          (ignoreBind (setAvailMovesWl (sortMoves moves))
            (ignoreBind (resetMoveRelated moves)
              (bind (stExPartition (splitDegree d k) allocs [] []) fun (ltk, gtk) =>
                bind (stExPartition moveRelatedSub ltk [] []) fun (ltkfreeze, ltksimp) =>
                  ignoreBind (setSpillWl gtk)
                    (ignoreBind (setSimpWl ltksimp)
                      (ignoreBind (setFreezeWl ltkfreeze) (ret allocs.length)))))))

/-- Literal `do_alloc1` (`reg_allocScript.sml:1288-1296`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_alloc1_def"]
def doAlloc1 (moves : List (Nat × (Nat × Nat))) (scost : Option (Spt Nat)) (k : Nat) :
    M State (List Nat) StateException :=
  bind getDim fun d =>
    bind (initAlloc1Heu moves d k) fun l =>
      ignoreBind (rptDoStep scost k l) (bind getStack fun st => ret st)

/-- Literal `biased_pref` (`reg_allocScript.sml:1369-1380`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "biased_pref_def"]
def biasedPref (mtable : Spt (List Nat)) (n : Nat) (ks : List Nat) :
    M State (Option Nat) StateException :=
  bind getDim fun d =>
    if n < d then
      bind (coalesceRoot n) fun v =>
        let vs := match sptLookup n mtable with
          | none => []
          | some vs => vs
        handleSubscript (firstMatchCol ks (v :: vs)) (ret none)
    else ret none

/-- Literal `do_reg_alloc` (`reg_allocScript.sml:1449-1462`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "do_reg_alloc_def"]
def doRegAlloc (alg : Algorithm) (scost : Option (Spt Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat))
    (fs : NumSet) : Spt Nat × Spt Nat × Nat → M State (Spt Nat) StateException
  | (ta, fa, n) =>
    ignoreBind (initRaState ct forced fs (ta, fa, n))
      (bind (ret (moves.map (updateMove (spDefault ta)))) fun moves0 =>
        bind (stExFilter (fun (m : Nat × (Nat × Nat)) => fullConsistencyOk k m.2.1 m.2.2)
            moves0 []) fun moves =>
          bind (doAlloc1 (if alg = .Simple then [] else moves) scost k) fun ls =>
            bind (ret (resortMoves (movesToSp moves0 .ln))) fun mvs =>
              ignoreBind (assignAtemps k ls (biasedPref mvs))
                (ignoreBind (assignStemps k (negBiasedPref k mvs))
                  (bind (extractColor ta) fun spcol => ret spcol)))

/-- Literal `reg_alloc_aux` (`reg_allocScript.sml:1473-1488`): run `do_reg_alloc`
on the generated initial state of dimension `n`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "reg_alloc_aux_def"]
def regAllocAux (alg : Algorithm) (scost : Option (Spt Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat))
    (fs : NumSet) : Spt Nat × Spt Nat × Nat → Translator.Monadic.MonadBase.Exc (Spt Nat) StateException
  | (ta, fa, n) =>
    runIraState (doRegAlloc alg scost k moves ct forced fs (ta, fa, n))
      { adj_ls := (n, []), node_tag := (n, .Atemp), degrees := (n, 0), dim := n,
        simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [],
        unavail_moves_wl := [], coalesced := (n, 0), move_related := (n, false), stack := [] }

/-- Literal `reg_alloc` (`reg_allocScript.sml:1490-1493`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "reg_alloc_def"]
def regAlloc (alg : Algorithm) (scost : Option (Spt Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat))
    (fs : NumSet) : Translator.Monadic.MonadBase.Exc (Spt Nat) StateException :=
  regAllocAux alg scost k moves ct forced fs (mkBij ct)

end Flapjack.RegAlloc
