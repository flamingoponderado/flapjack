import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.StateForeach

/-!
# reg_alloc degree, worklist and stack updates

Literal ports of `reg_allocScript.sml:252-319` and `650-666` over `ra_state`
and its generated accessors. HOL do-blocks are the accepted MonadBase
`bind`/`ignoreBind`/`ret`; `num` subtraction is truncated `Nat` subtraction;
`MEM`/`FILTER` use `decide`. Proof-side ports: the executed allocator is not
routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `dec_deg` (`reg_allocScript.sml:252-258`); `0 - 1 = 0`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def"]
def decDeg (n : Nat) : M State Unit StateException :=
  bind (degreesSub n) fun cd => updateDegrees n (cd - 1)

/-- Literal `dec_degree` (`reg_allocScript.sml:260-272`): decrement every
neighbour of an in-dimension node; out-of-dimension nodes are a no-op. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_degree_def"]
def decDegree (n : Nat) : M State Unit StateException :=
  bind getDim fun d =>
    if n < d then bind (adjLsSub n) fun adjs => stExForeach adjs decDeg
    else ret ()

/-- Literal `add_simp_wl` (`reg_allocScript.sml:274-280`): prepend. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "add_simp_wl_def"]
def addSimpWl (ls : List Nat) : M State Unit StateException :=
  bind getSimpWl fun swl => setSimpWl (ls ++ swl)

/-- Literal `add_spill_wl` (`reg_allocScript.sml:282-288`): prepend. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "add_spill_wl_def"]
def addSpillWl (ls : List Nat) : M State Unit StateException :=
  bind getSpillWl fun swl => setSpillWl (ls ++ swl)

/-- Literal `add_freeze_wl` (`reg_allocScript.sml:290-296`): prepend. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "add_freeze_wl_def"]
def addFreezeWl (ls : List Nat) : M State Unit StateException :=
  bind getFreezeWl fun fwl => setFreezeWl (ls ++ fwl)

/-- Literal `push_stack` (`reg_allocScript.sml:299-307`): read the stack,
zero the degree, clear the move flag, then push. A failing array update
stops before the push and keeps the earlier updates. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "push_stack_def"]
def pushStack (x : Nat) : M State Unit StateException :=
  bind getStack fun swl =>
    ignoreBind (updateDegrees x 0)
      (ignoreBind (updateMoveRelated x false) (setStack (x :: swl)))

/-- Literal `add_unavail_moves_wl` (`reg_allocScript.sml:309-315`): prepend. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "add_unavail_moves_wl_def"]
def addUnavailMovesWl (ls : List (Nat × (Nat × Nat))) : M State Unit StateException :=
  bind getUnavailMovesWl fun swl => setUnavailMovesWl (ls ++ swl)

/-- Literal `respill` (`reg_allocScript.sml:650-666`): a frozen node whose
degree reached `k` moves to the spill worklist, removing every copy from the
freeze worklist. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "respill_def"]
def respill (k x : Nat) : M State Unit StateException :=
  bind (degreesSub x) fun xd =>
    if xd < k then ret ()
    else
      bind getFreezeWl fun freeze =>
        if x ∈ freeze then
          ignoreBind (addSpillWl [x]) (setFreezeWl (freeze.filter (fun y => decide (y ≠ x))))
        else ret ()

end Flapjack.RegAlloc
