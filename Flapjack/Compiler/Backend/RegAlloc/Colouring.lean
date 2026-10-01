import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.StateForeach

/-!
# reg_alloc Atemp colouring

The first colouring pass of `reg_allocScript.sml:874-1005`: removing adjacent
colours, tagging one `Atemp` node, tagging all `Atemp` nodes, and the first fixed
colour among a node list. HOL `do` blocks are the accepted `st_ex_bind`
(`bind`), `st_ex_ignore_bind` (`ignoreBind`) and `st_ex_return` (`ret`); the
exception type is `state_exn` (`StateException`), as in the HOL types. HOL
`GENLIST (λx. x) n` is `List.range n` (`[0, ..., n - 1]`) and `FILTER P l` is
`l.filter P`. These are proof-side ports: the executed allocator is not routed
through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `remove_colours_def` (`reg_allocScript.sml:874-891`): with no
colours left the result is `[]`, with no nodes left it is the colours, and
otherwise each fixed neighbour colour is filtered out. The clauses keep HOL's
order, so the empty-colour clause takes priority. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "remove_colours_def"]
def removeColours : List Nat → List Nat → M State (List Nat) StateException
  | _, [] => ret []
  | [], ks => ret ks
  | x :: xs, ks =>
    bind (nodeTagSub x) (fun cx =>
      bind (match cx with
          | .Fixed c => removeColours xs (ks.filter fun y => y ≠ c)
          | _ => removeColours xs ks)
        (fun r => ret r))

/-- Exact HOL `assign_Atemp_tag_def` (`reg_allocScript.sml:896-919`): an `Atemp`
node with no remaining colour becomes `Stemp`; otherwise it is fixed to the
preference oracle's choice, or to the first remaining colour. Other nodes are
unchanged. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "assign_Atemp_tag_def"]
def assignAtempTag (ks : List Nat)
    (prefs : Nat → List Nat → M State (Option Nat) StateException) (n : Nat) :
    M State Unit StateException :=
  bind (nodeTagSub n) (fun ntag =>
    match ntag with
    | .Atemp =>
      bind (adjLsSub n) (fun adjs =>
        bind (removeColours adjs ks) (fun ks =>
          match ks with
          | [] => updateNodeTag n .Stemp
          | x :: _ =>
            bind (prefs n ks) (fun c =>
              match c with
              | none => updateNodeTag n (.Fixed x)
              | some y => updateNodeTag n (.Fixed y))))
    | _ => ret ())

/-- Exact HOL `assign_Atemps_def` (`reg_allocScript.sml:923-936`): tag the
in-range heuristic nodes first, then every node below `dim`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "assign_Atemps_def"]
def assignAtemps (k : Nat) (ls : List Nat)
    (prefs : Nat → List Nat → M State (Option Nat) StateException) :
    M State Unit StateException :=
  bind getDim (fun d =>
    bind (ret (ls.filter fun n => n < d)) (fun ls =>
      bind (ret (List.range k)) (fun ks =>
        bind (ret (List.range d)) (fun cs =>
          ignoreBind (stExForeach ls (assignAtempTag ks prefs))
            (stExForeach cs (assignAtempTag ks prefs))))))

/-- Exact HOL `first_match_col_def` (`reg_allocScript.sml:994-1003`): the first
fixed colour of a listed node that is among `ks`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "first_match_col_def"]
def firstMatchCol (ks : List Nat) : List Nat → M State (Option Nat) StateException
  | [] => ret none
  | x :: xs =>
    bind (nodeTagSub x) (fun c =>
      match c with
      | .Fixed m => if m ∈ ks then ret (some m) else firstMatchCol ks xs
      | _ => firstMatchCol ks xs)

end Flapjack.RegAlloc
