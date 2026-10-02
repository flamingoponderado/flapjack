import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Translator.Monadic.MonadBase
import Flapjack.Misc.Sptree
import Flapjack.Misc.ListEl
import Flapjack.Misc.Sorting
import Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts

/-!
# reg_alloc graph and state invariants

The invariant definitions of `reg_allocProofScript.sml` used by
`do_reg_alloc_correct`: edges, undirectedness, well-formed states, the
no-clash colouring invariant, preference oracles, cliques, subgraphs and
satisfactory colourings. HOL `bool` definitions are `Prop`s. The inverse-map pair
`sp_inverts`/`sp_inverts_insert` has its canonical port in
`Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts`.

HOL `EL` is the exact tagged `Flapjack.holEl` of `Flapjack.Misc.ListEl` (HOL
`listScript.sml` `EL_def`; `l[n]` within bounds, the opaque unspecified HOL `HD []`
beyond) and HOL `sorting$SORTED R` is the exact tagged `Flapjack.holSorted R` of
`Flapjack.Misc.Sorting` (`sortingScript.sml` `SORTED_DEF`), both cited in the pinned HOL
submodule (provenance bead flapjack-pxn.18.5.15.3.38.1). The `EL`-dependent declarations
were re-reviewed individually against the HOL source after that provenance approval
(bead flapjack-pxn.18.5.15.3.38.2).
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

instance : Inhabited Tag := ⟨.Atemp⟩

/-- Exact HOL `has_edge_def` (`reg_allocProofScript.sml:20-25`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "has_edge_def"]
def hasEdge (adjls : List (List Nat)) (x y : Nat) : Prop :=
  x < adjls.length ∧ y < adjls.length ∧ y ∈ holEl x adjls

/-- Exact HOL `undirected_def` (`reg_allocProofScript.sml:27-32`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "undirected_def"]
def undirected (adjls : List (List Nat)) : Prop :=
  ∀ x y, hasEdge adjls x y → hasEdge adjls y x

/-- Exact HOL `good_ra_state_def` (`reg_allocProofScript.sml:40-56`): every array has length
`dim`, every stored node is below `dim`, adjacency lists are strictly decreasing, and
the graph is undirected. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_ra_state_def"]
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

/-- Exact HOL `no_clash_def` (`reg_allocProofScript.sml:59-67`): adjacent nodes with fixed colours
have different colours. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_def"]
def noClash (adjLs : List (List Nat)) (nodeTag : List Tag) : Prop :=
  ∀ x y, hasEdge adjLs x y →
    match holEl x nodeTag, holEl y nodeTag with
    | .Fixed n, .Fixed m => n = m → x = y
    | _, _ => True

/-- Exact HOL `good_pref_def` (`reg_allocProofScript.sml:73-83`): on a good state the oracle
succeeds without changing the state and picks a member of its input list, if any. HOL's
three type variables are the implicit binders. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_pref_def"]
def goodPref {α β γ : Type} (pref : α → List β → M State (Option β) γ) : Prop :=
  ∀ n ks s, goodRaState s →
    ∃ res, pref n ks s = (.success res, s) ∧
      match res with
      | none => True
      | some k => k ∈ ks

/-- Exact HOL `good_neg_pref_def` (`reg_allocProofScript.sml:575-584`): the selected colour avoids
`bads` and is at least `k`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_neg_pref_def"]
def goodNegPref {α β : Type} (k : Nat) (pref : α → List Nat → M State (Option Nat) β) : Prop :=
  ∀ n bads s, goodRaState s →
    ∃ res, pref n bads s = (.success res, s) ∧
      match res with
      | none => True
      | some c => c ∉ bads ∧ k ≤ c

/-- Exact HOL `is_clique_def` (`reg_allocProofScript.sml:983-987`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_clique_def"]
def isClique (ls : List Nat) (adjls : List (List Nat)) : Prop :=
  ∀ x y, x ∈ ls ∧ y ∈ ls ∧ x ≠ y → hasEdge adjls x y

/-- Exact HOL `is_subgraph_def` (`reg_allocProofScript.sml:989-993`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_def"]
def isSubgraph (g h : List (List Nat)) : Prop :=
  ∀ x y, hasEdge g x y → hasEdge h x y

/-- Exact HOL `is_subgraph_refl` (`reg_allocProofScript.sml:995-999`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_refl"]
theorem isSubgraphRefl (s : List (List Nat)) : isSubgraph s s :=
  fun _ _ h => h

/-- Exact HOL `is_subgraph_trans` (`reg_allocProofScript.sml:1001-1008`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "is_subgraph_trans"]
theorem isSubgraphTrans (s s' s'' : List (List Nat)) :
    isSubgraph s s' ∧ isSubgraph s' s'' → isSubgraph s s'' :=
  fun ⟨h1, h2⟩ x y h => h2 x y (h1 x y h)

/-- Exact HOL `hide_def` (`reg_allocProofScript.sml:1010-1012`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "hide_def"]
def hide {α : Type} (x : α) : α := x

/-- Exact HOL `colouring_satisfactory_def` (`reg_allocProofScript.sml:1236-1241`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "colouring_satisfactory_def"]
def colouringSatisfactory {α : Type} (col : Nat → α) (adjls : List (List Nat)) : Prop :=
  ∀ x, x < adjls.length →
    ∀ y, y < adjls.length ∧ y ∈ holEl x adjls → col x = col y → x = y

end Flapjack.RegAlloc
