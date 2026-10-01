import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.ExceptionFunctions
import Flapjack.Compiler.Backend.RegAlloc.StateForeach
import Flapjack.Compiler.Backend.RegAlloc.StateMap
import Flapjack.Basis.Pure.MlList
import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.RegAlloc.TagColour

/-!
# reg_alloc Stemp colouring

The second colouring pass of `reg_allocScript.sml:938-992` and the negative
preference oracle of `reg_allocScript.sml:1419-1446`: tagging one `Stemp` node,
tagging all nodes, and the first-match/biased negative preferences. `tag_col` and
`unbound_colour` are the canonical ports of `RegAlloc.TagColour`. HOL `do` blocks are the accepted
`bind`/`ret`; `sort` is `mllist$sort` (`Basis.Pure.MlList.sort`), `GENLIST (λx. x) n`
is `List.range n`, `MAP f l` is `l.map f` and `lookup` is `sptLookup`. These are
proof-side ports: the executed allocator is not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `assign_Stemp_tag_def` (`reg_allocScript.sml:959-980`): a `Stemp`
node is fixed to the oracle's choice, or else to the first colour from `k` not
used by a neighbour. Other nodes are unchanged. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "assign_Stemp_tag_def"]
def assignStempTag (k : Nat) (prefs : Nat → List Nat → M State (Option Nat) StateException)
    (n : Nat) : M State Unit StateException :=
  bind (nodeTagSub n) (fun ntag =>
    match ntag with
    | .Stemp =>
      bind (adjLsSub n) (fun adjs =>
        bind (stExMap nodeTagSub adjs) (fun tags =>
          let bads := Basis.Pure.MlList.sort (fun x y => decide (x ≤ y)) (tags.map tagCol)
          bind (prefs n bads) (fun c =>
            match c with
            | none => updateNodeTag n (.Fixed (unboundColour k bads))
            | some y => updateNodeTag n (.Fixed y))))
    | _ => ret ())

/-- Exact HOL `assign_Stemps_def` (`reg_allocScript.sml:984-990`): tag every node
below `dim`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "assign_Stemps_def"]
def assignStemps (k : Nat) (prefs : Nat → List Nat → M State (Option Nat) StateException) :
    M State Unit StateException :=
  bind getDim (fun d =>
    bind (ret (List.range d)) (fun cs =>
      stExForeach cs (assignStempTag k prefs)))

/-- Exact HOL `neg_first_match_col_def` (`reg_allocScript.sml:1419-1430`): the first
fixed colour of a listed node that is neither in `bads` nor below `k`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "neg_first_match_col_def"]
def negFirstMatchCol (k : Nat) (bads : List Nat) : List Nat → M State (Option Nat) StateException
  | [] => ret none
  | x :: xs =>
    bind (nodeTagSub x) (fun c =>
      match c with
      | .Fixed m => if m ∈ bads ∨ m < k then negFirstMatchCol k bads xs else ret (some m)
      | _ => negFirstMatchCol k bads xs)

/-- Exact HOL `neg_biased_pref_def` (`reg_allocScript.sml:1432-1446`): for an
in-range node, the first acceptable colour among its move partners in `mtable`,
with an out-of-range partner treated as no preference. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "neg_biased_pref_def"]
def negBiasedPref (k : Nat) (mtable : Spt (List Nat)) (n : Nat) (bads : List Nat) :
    M State (Option Nat) StateException :=
  bind getDim (fun d =>
    if n < d then
      let vs := match sptLookup n mtable with
        | none => []
        | some vs => vs
      handleSubscript (negFirstMatchCol k bads vs) (ret none)
    else ret none)

end Flapjack.RegAlloc
