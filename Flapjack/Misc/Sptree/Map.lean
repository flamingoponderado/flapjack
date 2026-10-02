import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal payload-only Spt map. Unlike indexed `mapi0`, this source operation
preserves every tree constructor, including malformed empty internal nodes.
Input and output payload types are independent and no well-formedness premise
is required. The executed allocator route remains a separate dependency. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "map_def"]
def sptMap {α β : Type} (f : α → β) : Spt α → Spt β
  | .ln => .ln
  | .ls value => .ls (f value)
  | .bn left right => .bn (sptMap f left) (sptMap f right)
  | .bs left value right => .bs (sptMap f left) (f value) (sptMap f right)

/-- Exact HOL `lookup_map` (`sptreeScript.sml:1565-1569`, pinned HOL submodule);
`f` is free in HOL. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "lookup_map"]
theorem sptLookup_sptMap {α β : Type} (f : α → β) :
    ∀ (s : Spt α) (x : Nat), sptLookup x (sptMap f s) = (sptLookup x s).map f := by
  intro s
  induction s with
  | ln => intro x; rfl
  | ls v => intro x; simp only [sptMap, sptLookup]; split <;> rfl
  | bn l r ihl ihr =>
      intro x; simp only [sptMap, sptLookup]
      split
      · rfl
      · split
        · exact ihl _
        · exact ihr _
  | bs l v r ihl ihr =>
      intro x; simp only [sptMap, sptLookup]
      split
      · rfl
      · split
        · exact ihl _
        · exact ihr _

/-- Exact HOL `wf_map` (`sptreeScript.sml:1575-1578`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_map"]
theorem sptWfMap {α β : Type} : ∀ (t : Spt α) (f : α → β), sptWf (sptMap f t) = sptWf t := by
  intro t f
  have he : ∀ u : Spt α, sptIsEmpty (sptMap f u) = sptIsEmpty u := fun u => by
    cases u <;> rfl
  induction t with
  | ln => rfl
  | ls _ => rfl
  | bn l r ihl ihr => simp only [sptMap, sptWf, ihl, ihr, he]
  | bs l _ r ihl ihr => simp only [sptMap, sptWf, ihl, ihr, he]

end Flapjack
