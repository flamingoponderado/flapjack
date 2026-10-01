import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Translator.Monadic.MonadBase
import Flapjack.Misc.Sptree

/-!
# reg_alloc graph and state invariants

The invariant definitions of `reg_allocProofScript.sml` used by
`do_reg_alloc_correct`: edges, undirectedness, well-formed states, the
no-clash colouring invariant, preference oracles, inverse maps, cliques,
subgraphs and satisfactory colourings. HOL `bool` definitions are `Prop`s.

HOL `EL n l` is `l[n]` when `n < LENGTH l` and otherwise `HD []`, because
`TL [] = []` (`HOL/src/list/src/listScript.sml` `HD`, `TL_DEF`, `EL_def`). Here it
is `holEl`, with `HD []` an unspecified opaque constant (`hdNil`). HOL
`sorting$SORTED R` is `holSorted R`, which follows `SORTED_DEF` clause by clause.
Both are provisional, untagged Flapjack infrastructure, not completed HOL ports.
The HOL standard-library `listScript.sml` source is outside the reference
checker's reviewed external paths. Its exact `HD`/`EL` tags wait on the
provenance approval of beads flapjack-pxn.18.5.15.3.38 and .38.1. Until that
approval lands, the `has_edge`, `no_clash` and `colouring_satisfactory` ports
below depend on this unreviewed `EL` rendering, and their acceptance is held
on bead .38. `holSorted` follows the original `sortingScript.sml` `SORTED_DEF`
(adjacent pairs plus the recursive tail, with no transitivity assumption). It
is likewise untagged.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Provisional rendering of HOL `HD ([] : α list)`: one fixed value of each
type whose identity HOL leaves unspecified. It is opaque, so no property beyond
its type is provable. Untagged pending the listScript provenance approval
(bead flapjack-pxn.18.5.15.3.38.1); not an approved HOL dependency. -/
opaque hdNil (α : Type) [Inhabited α] : α

/-- Provisional rendering of HOL `EL n l`: the `n`-th element, and `HD []`
beyond the end (HOL `TL [] = []`). Untagged pending bead
flapjack-pxn.18.5.15.3.38.1; not an approved HOL dependency. -/
def holEl {α : Type} [Inhabited α] (n : Nat) (l : List α) : α :=
  l.getD n (hdNil α)

/-- HOL `sorting$SORTED R`: every adjacent pair is related. -/
def holSorted {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ holSorted R (y :: rest)

instance : Inhabited Tag := ⟨.Atemp⟩

/-- Exact HOL `has_edge_def` (`reg_allocProofScript.sml:20-25`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "has_edge_def"]
def hasEdge (adjls : List (List Nat)) (x y : Nat) : Prop :=
  x < adjls.length ∧ y < adjls.length ∧ y ∈ holEl x adjls

/-- Exact HOL `undirected_def` (`reg_allocProofScript.sml:27-32`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "undirected_def"]
def undirected (adjls : List (List Nat)) : Prop :=
  ∀ x y, hasEdge adjls x y → hasEdge adjls y x

/-- Exact HOL `good_ra_state_def` (`reg_allocProofScript.sml:40-56`): every
array has length `dim`, every stored node is below `dim`, adjacency lists are
strictly decreasing, and the graph is undirected. -/
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

/-- Exact HOL `no_clash_def` (`reg_allocProofScript.sml:59-67`): adjacent nodes
with fixed colours have different colours. The tags are read with HOL `EL`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "no_clash_def"]
def noClash (adjLs : List (List Nat)) (nodeTag : List Tag) : Prop :=
  ∀ x y, hasEdge adjLs x y →
    match holEl x nodeTag, holEl y nodeTag with
    | .Fixed n, .Fixed m => n = m → x = y
    | _, _ => True

/-- Exact HOL `good_pref_def` (`reg_allocProofScript.sml:73-83`): on a good
state the oracle succeeds without changing the state and picks a member of
its input list, if any. HOL's three type variables are the implicit binders. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_pref_def"]
def goodPref {α β γ : Type} (pref : α → List β → M State (Option β) γ) : Prop :=
  ∀ n ks s, goodRaState s →
    ∃ res, pref n ks s = (.success res, s) ∧
      match res with
      | none => True
      | some k => k ∈ ks

/-- Exact HOL `good_neg_pref_def` (`reg_allocProofScript.sml:575-584`): the
selected colour avoids `bads` and is at least `k`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "good_neg_pref_def"]
def goodNegPref {α β : Type} (k : Nat) (pref : α → List Nat → M State (Option Nat) β) : Prop :=
  ∀ n bads s, goodRaState s →
    ∃ res, pref n bads s = (.success res, s) ∧
      match res with
      | none => True
      | some c => c ∉ bads ∧ k ≤ c

/-- Exact HOL `sp_inverts_def` (`reg_allocProofScript.sml:783-788`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_def"]
def spInverts (f g : Spt Nat) : Prop :=
  ∀ m fm, sptLookup m f = some fm → sptLookup fm g = some m

/-- Exact HOL `sp_inverts_insert` (`reg_allocProofScript.sml:790-800`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "sp_inverts_insert"]
theorem spInvertsInsert (f g : Spt Nat) (x y : Nat) :
    spInverts f g ∧ ¬ sptDomain f x ∧ ¬ sptDomain g y →
      spInverts (sptInsert x y f) (sptInsert y x g) := by
  rintro ⟨h, hx, hy⟩ m fm hm
  by_cases hmx : m = x
  · subst hmx
    rw [sptLookup_sptInsert_same] at hm
    cases hm
    rw [sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne _ _ _ _ hmx] at hm
    have hg := h m fm hm
    have hfy : fm ≠ y := by
      rintro rfl
      exact hy (by simp [sptDomain, hg])
    rw [sptLookup_sptInsert_ne _ _ _ _ hfy, hg]

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
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "colouring_satisfactory_def"]
def colouringSatisfactory {α : Type} (col : Nat → α) (adjls : List (List Nat)) : Prop :=
  ∀ x, x < adjls.length →
    ∀ y, y < adjls.length ∧ y ∈ holEl x adjls → col x = col y → x = y

end Flapjack.RegAlloc
