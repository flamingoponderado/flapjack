import Flapjack.Compiler.Backend.RegAlloc.ConsideredVar
import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.Compiler.Backend.RegAlloc.StateForeach

/-!
# reg_alloc coalescing helpers

Literal ports of `reg_allocScript.sml:418-424` (`inc_deg`), `565-648`
(`consistency_ok`, `coalesce_parent`, `canonize_move`, `st_ex_FIRST`) and
`708-724` (`reset_move_related`) over `ra_state` and its generated accessors.
HOL do-blocks are the accepted MonadBase `bind`/`ignoreBind`/`ret`; pattern
binders `(x, y) <- m` and `let (p, (x, y)) = m` are pattern matches;
`COUNT_LIST d` is `List.range d`. Proof-side ports: the executed allocator is
not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `inc_deg` (`reg_allocScript.sml:418-424`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "inc_deg_def"]
def incDeg (n d : Nat) : M State Unit StateException :=
  bind (degreesSub n) fun cd => updateDegrees n (cd + d)

/-- Literal `consistency_ok` (`reg_allocScript.sml:565-582`): distinct, not
already adjacent (by the early-stop `sorted_mem` on `y`'s list), each fixed or
move related, and not both fixed. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "consistency_ok_def"]
def consistencyOk (x y : Nat) : M State Bool StateException :=
  if x = y then ret false
  else
    bind (adjLsSub y) fun adjy =>
      if sortedMem x adjy then ret false
      else
        bind (isFixed x) fun bx =>
          bind (isFixed y) fun by_ =>
            bind (moveRelatedSub x) fun movrelx =>
              bind (moveRelatedSub y) fun movrely =>
                ret ((bx || movrelx) && (by_ || movrely) && !(bx && by_))

/-- Literal `coalesce_parent` (`reg_allocScript.sml:589-607`): follow the
coalesce chain to a fixed target or a self/forward pointer, compressing the
path on the way back. Recursion is on strictly smaller nodes, as HOL's
termination argument uses. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "coalesce_parent_def"]
def coalesceParent (x : Nat) : M State Nat StateException :=
  bind (coalescedSub x) fun xt =>
    bind (isFixed xt) fun bx =>
      if bx then ret xt
      else if _h : x ≤ xt then ret x
      else
        bind (coalesceParent xt) fun anc =>
          ignoreBind (updateCoalesced x anc) (ret anc)
termination_by x
decreasing_by omega

/-- Literal `canonize_move` (`reg_allocScript.sml:609-618`): a fixed endpoint
first, otherwise the smaller node first. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "canonize_move_def"]
def canonizeMove (x y : Nat) : M State (Nat × Nat) StateException :=
  bind (isFixed x) fun bx =>
    bind (isFixed y) fun by_ =>
      if by_ then ret (y, x)
      else if bx then ret (x, y)
      else if x < y then ret (x, y)
      else ret (y, x)

/-- Literal `st_ex_FIRST` (`reg_allocScript.sml:626-648`): the first move whose
canonical root pair passes `P` and `Q`. Moves failing `P` are dropped; moves
passing `P` but not `Q` are prepended to `unavail` in canonical form. The
move priority and `Q`'s payload are arbitrary, as in the original type. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_FIRST_def"]
def stExFirst {α β : Type} (P : Nat → Nat → M State Bool StateException)
    (Q : Nat → Nat → M State (Option α) StateException) :
    List (β × (Nat × Nat)) → List (β × (Nat × Nat)) →
      M State (Option ((Nat × Nat) × α × List (β × (Nat × Nat))) × List (β × (Nat × Nat)))
        StateException
  | [], unavail => ret (none, unavail)
  | m :: ms, unavail =>
    let (p, (x, y)) := m
    bind (coalesceParent x) fun x =>
      bind (coalesceParent y) fun y =>
        bind (P x y) fun b1 =>
          if ¬b1 then stExFirst P Q ms unavail
          else
            bind (canonizeMove x y) fun (x, y) =>
              bind (Q x y) fun optb2 =>
                match optb2 with
                | none => stExFirst P Q ms ((p, (x, y)) :: unavail)
                | some pr => ret (some ((x, y), pr, ms), unavail)

/-- Literal `reset_move_related` (`reg_allocScript.sml:708-724`): clear every
flag below `dim`, then mark each non-fixed endpoint of the given moves. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "reset_move_related_def"]
def resetMoveRelated {α : Type} (ls : List (α × (Nat × Nat))) : M State Unit StateException :=
  bind getDim fun d =>
    ignoreBind (stExForeach (List.range d) fun x => updateMoveRelated x false)
      (stExForeach ls fun (_, (x, y)) =>
        bind (isFixed x) fun bx =>
          bind (isFixed y) fun by_ =>
            ignoreBind (updateMoveRelated x (!bx)) (updateMoveRelated y (!by_)))

end Flapjack.RegAlloc
