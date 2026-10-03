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

/-- Exact HOL `domain_map` (`sptreeScript.sml:1561-1563`):
`!s. domain (map f s) = domain s`, with `f` free. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "domain_map"]
theorem sptDomain_sptMap {α β : Type} (f : α → β) :
    ∀ (s : Spt α), sptDomain (sptMap f s) = sptDomain s := by
  intro s
  funext k
  simp only [sptDomain, sptLookup_sptMap, Option.isSome_map]

/-- Exact HOL `map_insert` (`sptreeScript.sml:1586-1602`). -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "map_insert"]
theorem sptMap_sptInsert {α β : Type} :
    ∀ (f : α → β) (x : Nat) (y : α) (z : Spt α),
      sptMap f (sptInsert x y z) = sptInsert x (f y) (sptMap f z) := by
  intro f x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro y z
    by_cases hx : x = 0
    · subst hx
      cases z <;> simp [sptInsert, sptMap]
    · have hlt : (x - 1) / 2 < x := by omega
      cases z <;> simp only [sptMap] <;>
        rw [sptInsert.eq_def x (f y), sptInsert.eq_def x y] <;>
        by_cases h2 : x % 2 = 0 <;> simp only [hx, h2, if_true, if_false, sptMap, ih _ hlt]

/-- Exact HOL `map_fromAList` (`sptreeScript.sml:1604-1610`). -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "map_fromAList"]
theorem sptMap_sptFromAList {α β : Type} (f : α → β) (ls : List (Nat × α)) :
    sptMap f (sptFromAList ls) =
      sptFromAList (ls.map (fun p => match p with | (k, v) => (k, f v))) := by
  induction ls with
  | nil => rfl
  | cons p ls ih =>
    obtain ⟨k, v⟩ := p
    simp only [sptFromAList, List.map, sptMap_sptInsert, ih]

/-- Exact HOL `map_union` (`sptreeScript.sml:1786-1791`), with `f` free. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "map_union"]
theorem sptMap_sptUnion {α β : Type} (f : α → β) :
    ∀ (t1 t2 : Spt α), sptMap f (sptUnion t1 t2) = sptUnion (sptMap f t1) (sptMap f t2) := by
  intro t1
  induction t1 with
  | ln => intro t2; simp only [sptUnion, sptMap]
  | ls v => intro t2; cases t2 <;> simp only [sptUnion, sptMap]
  | bn l r ihl ihr => intro t2; cases t2 <;> simp only [sptUnion, sptMap, ihl, ihr]
  | bs l v r ihl ihr => intro t2; cases t2 <;> simp only [sptUnion, sptMap, ihl, ihr]

end Flapjack
