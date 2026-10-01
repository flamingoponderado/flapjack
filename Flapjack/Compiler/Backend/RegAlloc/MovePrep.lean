import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar
import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.Compiler.Backend.RegAlloc.StateMap
import Flapjack.Compiler.Backend.RegAlloc.TagColour
import Flapjack.Misc.Sptree.ToAList

/-!
# reg_alloc colour extraction and move preprocessing

Literal ports of `reg_allocScript.sml:1306-1416`: `extract_color`,
`coalesce_root`, `full_consistency_ok` and `update_move`, over `ra_state` and
its generated accessors. HOL do-blocks are the accepted MonadBase
`bind`/`ret`, literal `x <- return e` binders `bind (ret e)`. Proof-side ports:
the executed allocator is not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `extract_color` (`reg_allocScript.sml:1306-1317`): each mapped
node's fixed colour, as a sparse map. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "extract_color_def"]
def extractColor (ta : Spt Nat) : M State (Spt Nat) StateException :=
  bind (ret (sptToAList ta)) fun taa =>
    bind (stExMap (fun (k, v) => bind (nodeTagSub v) fun t => ret (k, extractTag t)) taa)
      fun itags => ret (sptFromAList itags)

/-- Literal `coalesce_root` (`reg_allocScript.sml:1353-1366`): the read-only
`coalesce_parent`, by well-founded recursion on strictly smaller nodes. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "coalesce_root_def"]
def coalesceRoot (x : Nat) : M State Nat StateException :=
  bind (coalescedSub x) fun xt =>
    bind (isFixed xt) fun bx =>
      if bx then ret xt
      else if _h : x ≤ xt then ret x
      else coalesceRoot xt
termination_by x
decreasing_by omega

/-- Literal `full_consistency_ok` (`reg_allocScript.sml:1385-1406`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "full_consistency_ok_def"]
def fullConsistencyOk (k x y : Nat) : M State Bool StateException :=
  if x = y then ret false
  else
    bind getDim fun d =>
      if x ≥ d ∨ y ≥ d then ret false
      else
        bind (adjLsSub y) fun adjy =>
          if sortedMem x adjy then ret false
          else
            bind (isFixedK k x) fun bx =>
              bind (isFixedK k y) fun by_ =>
                bind (isAtemp x) fun ax =>
                  bind (isAtemp y) fun ay =>
                    ret ((bx || ax) && (by_ || ay) && !(bx && by_))

/-- Literal `update_move` (`reg_allocScript.sml:1409-1416`): rename both
endpoints and order them. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_move_def"]
def updateMove (spta : Nat → Nat) : Nat × (Nat × Nat) → Nat × (Nat × Nat)
  | (p, (x, y)) =>
    let spx := spta x
    let spy := spta y
    if spx ≤ spy then (p, (spx, spy)) else (p, (spy, spx))

end Flapjack.RegAlloc
