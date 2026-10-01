import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Translator.Monadic.MonadBase
import Flapjack.Misc.Sptree
import Flapjack.Misc.ListEl
import Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts

/-!
# reg_alloc graph and state invariants

The invariant definitions of `reg_allocProofScript.sml` used by
`do_reg_alloc_correct`: edges, undirectedness, well-formed states, the
no-clash colouring invariant, preference oracles, cliques, subgraphs and
satisfactory colourings. HOL `bool` definitions are `Prop`s. The inverse-map pair
`sp_inverts`/`sp_inverts_insert` has its canonical port in
`Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts`.

HOL `EL` is the shared untagged rendering `Flapjack.holEl` of `Flapjack.Misc.ListEl`
(`l[n]` within bounds, the opaque unspecified HOL `HD []` beyond), and HOL
`sorting$SORTED R` is `holSorted R`, which follows the original `sortingScript.sml`
`SORTED_DEF` clause by clause (adjacent pairs plus the recursive tail, with no
transitivity assumption). Both are provisional, untagged infrastructure, not completed HOL
ports: the HOL standard-library list and sorting sources are outside the reference
checker's reviewed external paths, and the exact `HD`/`EL` tags wait on the provenance
approval of beads flapjack-pxn.18.5.15.3.38 and .38.1. Every declaration below except
`hide` depends on `EL`, directly or through `has_edge`/`good_ra_state`, so those are
untagged and their acceptance is held on bead .38.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- HOL `sorting$SORTED R`: every adjacent pair is related. -/
def holSorted {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ holSorted R (y :: rest)

instance : Inhabited Tag := ⟨.Atemp⟩

/-- HOL `has_edge_def` (`reg_allocProofScript.sml:20-25`).

Provisional and untagged: this ports HOL `has_edge_def` but its statement reads HOL `EL`
through `holEl`, whose HOL `listScript` provenance is pending review (bead
flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that review is accepted. -/
def hasEdge (adjls : List (List Nat)) (x y : Nat) : Prop :=
  x < adjls.length ∧ y < adjls.length ∧ y ∈ holEl x adjls

/-- HOL `undirected_def` (`reg_allocProofScript.sml:27-32`).

Provisional and untagged: this ports HOL `undirected_def` but it is stated through
`has_edge`, which reads HOL `EL` through `holEl`, whose HOL `listScript` provenance is
pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that
review is accepted. -/
def undirected (adjls : List (List Nat)) : Prop :=
  ∀ x y, hasEdge adjls x y → hasEdge adjls y x

/-- HOL `good_ra_state_def` (`reg_allocProofScript.sml:40-56`): every array has length
`dim`, every stored node is below `dim`, adjacency lists are strictly decreasing, and
the graph is undirected.

Provisional and untagged: this ports HOL `good_ra_state_def` but it is stated through
`undirected`/`has_edge` (HOL `EL` via `holEl`) and HOL `SORTED` via `holSorted`, whose
HOL `listScript` provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1).
Restore the `@[hol]` tag once that review is accepted. -/
def goodRaState (s : State) : Prop :=
  s.adj_ls.length = s.dim ∧
  s.node_tag.length = s.dim ∧
  s.degrees.length = s.dim ∧
  s.coalesced.length = s.dim ∧
  s.move_related.length = s.dim ∧
  (∀ v ∈ s.coalesced, v < s.dim) ∧
  (∀ ls ∈ s.adj_ls, ∀ v ∈ ls, v < s.dim) ∧
  (∀ ls ∈ s.adj_ls, holSorted (· > ·) ls) ∧
  (∀ v ∈ s.simp_wl, v < s.dim) ∧
  (∀ v ∈ s.spill_wl, v < s.dim) ∧
  (∀ v ∈ s.freeze_wl, v < s.dim) ∧
  (∀ m ∈ s.avail_moves_wl, m.2.1 < s.dim ∧ m.2.2 < s.dim) ∧
  (∀ m ∈ s.unavail_moves_wl, m.2.1 < s.dim ∧ m.2.2 < s.dim) ∧
  undirected s.adj_ls

/-- HOL `no_clash_def` (`reg_allocProofScript.sml:59-67`): adjacent nodes with fixed colours
have different colours.

Provisional and untagged: this ports HOL `no_clash_def` but its statement reads HOL `EL`
through `holEl`, whose HOL `listScript` provenance is pending review (bead
flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that review is accepted. -/
def noClash (adjLs : List (List Nat)) (nodeTag : List Tag) : Prop :=
  ∀ x y, hasEdge adjLs x y →
    match holEl x nodeTag, holEl y nodeTag with
    | .Fixed n, .Fixed m => n = m → x = y
    | _, _ => True

/-- HOL `good_pref_def` (`reg_allocProofScript.sml:73-83`): on a good state the oracle
succeeds without changing the state and picks a member of its input list, if any. HOL's
three type variables are the implicit binders.

Provisional and untagged: this ports HOL `good_pref_def` but it is stated through
`good_ra_state`, which depends on HOL `EL` via `holEl`, whose HOL `listScript`
provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]`
tag once that review is accepted. -/
def goodPref {α β γ : Type} (pref : α → List β → M State (Option β) γ) : Prop :=
  ∀ n ks s, goodRaState s →
    ∃ res, pref n ks s = (.success res, s) ∧
      match res with
      | none => True
      | some k => k ∈ ks

/-- HOL `good_neg_pref_def` (`reg_allocProofScript.sml:575-584`): the selected colour avoids
`bads` and is at least `k`.

Provisional and untagged: this ports HOL `good_neg_pref_def` but it is stated through
`good_ra_state`, which depends on HOL `EL` via `holEl`, whose HOL `listScript`
provenance is pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]`
tag once that review is accepted. -/
def goodNegPref {α β : Type} (k : Nat) (pref : α → List Nat → M State (Option Nat) β) : Prop :=
  ∀ n bads s, goodRaState s →
    ∃ res, pref n bads s = (.success res, s) ∧
      match res with
      | none => True
      | some c => c ∉ bads ∧ k ≤ c

/-- HOL `is_clique_def` (`reg_allocProofScript.sml:983-987`).

Provisional and untagged: this ports HOL `is_clique_def` but it is stated through
`has_edge`, which reads HOL `EL` through `holEl`, whose HOL `listScript` provenance is
pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that
review is accepted. -/
def isClique (ls : List Nat) (adjls : List (List Nat)) : Prop :=
  ∀ x y, x ∈ ls ∧ y ∈ ls ∧ x ≠ y → hasEdge adjls x y

/-- HOL `is_subgraph_def` (`reg_allocProofScript.sml:989-993`).

Provisional and untagged: this ports HOL `is_subgraph_def` but it is stated through
`has_edge`, which reads HOL `EL` through `holEl`, whose HOL `listScript` provenance is
pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that
review is accepted. -/
def isSubgraph (g h : List (List Nat)) : Prop :=
  ∀ x y, hasEdge g x y → hasEdge h x y

/-- HOL `is_subgraph_refl` (`reg_allocProofScript.sml:995-999`).

Provisional and untagged: this ports HOL `is_subgraph_refl` but it is stated through
`is_subgraph`/`has_edge` (HOL `EL` via `holEl`), whose HOL `listScript` provenance is
pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that
review is accepted. -/
theorem isSubgraphRefl (s : List (List Nat)) : isSubgraph s s :=
  fun _ _ h => h

/-- HOL `is_subgraph_trans` (`reg_allocProofScript.sml:1001-1008`).

Provisional and untagged: this ports HOL `is_subgraph_trans` but it is stated through
`is_subgraph`/`has_edge` (HOL `EL` via `holEl`), whose HOL `listScript` provenance is
pending review (bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that
review is accepted. -/
theorem isSubgraphTrans (s s' s'' : List (List Nat)) :
    isSubgraph s s' ∧ isSubgraph s' s'' → isSubgraph s s'' :=
  fun ⟨h1, h2⟩ x y h => h2 x y (h1 x y h)

/-- Exact HOL `hide_def` (`reg_allocProofScript.sml:1010-1012`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "hide_def"]
def hide {α : Type} (x : α) : α := x

/-- HOL `colouring_satisfactory_def` (`reg_allocProofScript.sml:1236-1241`).

Provisional and untagged: this ports HOL `colouring_satisfactory_def` but its statement
reads HOL `EL` through `holEl`, whose HOL `listScript` provenance is pending review
(bead flapjack-pxn.18.5.15.3.38.1). Restore the `@[hol]` tag once that review is
accepted. -/
def colouringSatisfactory {α : Type} (col : Nat → α) (adjls : List (List Nat)) : Prop :=
  ∀ x, x < adjls.length →
    ∀ y, y < adjls.length ∧ y ∈ holEl x adjls → col x = col y → x = y

end Flapjack.RegAlloc
