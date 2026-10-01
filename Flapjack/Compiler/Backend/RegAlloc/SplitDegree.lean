import Flapjack.Compiler.Backend.RegAlloc.Accessors

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `is_not_coalesced` (`reg_allocScript.sml:322-327`): a node is its
own coalesce target. Out-of-range nodes fail with `Subscript`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_not_coalesced_def"]
def isNotCoalesced (d : Nat) : M State Bool StateException :=
  bind (coalescedSub d) fun dt => ret (decide (d = dt))

/-- Literal `split_degree` (`reg_allocScript.sml:330-340`): for `v < d`, low
degree and not coalesced; any `v ≥ d` returns `true` without reading state. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "split_degree_def"]
def splitDegree (d k v : Nat) : M State Bool StateException :=
  if v < d then
    bind (degreesSub v) fun vd =>
      bind (isNotCoalesced v) fun b => ret (decide (vd < k) && b)
  else ret true

end Flapjack.RegAlloc
