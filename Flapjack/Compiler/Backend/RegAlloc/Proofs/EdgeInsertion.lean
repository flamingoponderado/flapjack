import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.GraphConstruction
import Flapjack.Compiler.Backend.RegAlloc.SortedInsert
import Flapjack.Compiler.Backend.RegAlloc.SortedMem
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Misc.Sorting

/-!
# reg_allocProof: sorted adjacency lists and edge insertion

Ports of `reg_allocProofScript.sml:1020-1166`: strictly decreasing adjacency
lists stay sorted under `sorted_insert`, `sorted_mem` decides membership on
them, and inserting edges into a `good_ra_state` graph keeps it good while
adding exactly the new edges. HOL `SORTED $>` is the exact `holSorted (· > ·)`,
`MEM` list membership, `EVERY P l` is `∀ x ∈ l, P x`, `REVERSE` `List.reverse`,
HOL `EL` the exact `holEl`, and `hide` the exact tagged `hide`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

private theorem gtTransitive : holTransitive (fun (a b : Nat) => a > b) :=
  fun _ _ _ ⟨h1, h2⟩ => Nat.lt_trans h2 h1

/-- Exact HOL `GT_sorted_eq` (`reg_allocProofScript.sml:1020-1025`); `x` and `L`
are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "GT_sorted_eq"]
theorem gtSortedEq (x : Nat) (L : List Nat) :
    holSorted (· > ·) (x :: L) ↔ holSorted (· > ·) L ∧ ∀ y, y ∈ L → x > y :=
  holSortedEq _ L x gtTransitive

/-- `SORTED` of an append, for the strict order on numbers. -/
private theorem sorted_append :
    ∀ (l1 l2 : List Nat),
      holSorted (· > ·) (l1 ++ l2) ↔
        holSorted (· > ·) l1 ∧ holSorted (· > ·) l2 ∧ ∀ a ∈ l1, ∀ b ∈ l2, a > b
  | [], l2 => by simp [holSorted]
  | a :: l1, l2 => by
      rw [List.cons_append, gtSortedEq, gtSortedEq, sorted_append l1 l2]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        refine ⟨⟨h1, fun y hy => h4 y (List.mem_append_left _ hy)⟩, h2, fun c hc b hb => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact h4 b (List.mem_append_right _ hb)
        · exact h3 c hc b hb
      · rintro ⟨⟨h1, h4⟩, h2, h3⟩
        refine ⟨⟨h1, h2, fun c hc b hb => h3 c (List.mem_cons_of_mem _ hc) b hb⟩,
          fun y hy => ?_⟩
        rcases List.mem_append.mp hy with hy | hy
        · exact h4 y hy
        · exact h3 a List.mem_cons_self y hy

/-- Exact HOL `sorted_insert_correct_lem` (`reg_allocProofScript.sml:1027-1072`);
`x` is free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "sorted_insert_correct_lem"]
theorem sortedInsertCorrectLem (x : Nat) :
    ∀ (ls acc : List Nat),
      holSorted (· > ·) ls ∧ holSorted (· > ·) acc.reverse ∧
      holSorted (· > ·) (acc.reverse ++ ls) ∧ (∀ y ∈ acc, y > x) →
      hide (holSorted (· > ·) (sortedInsert x acc ls) ∧
        ∀ z, z ∈ sortedInsert x acc ls ↔ x = z ∨ z ∈ ls ∨ z ∈ acc) := by
  intro ls
  induction ls with
  | nil =>
      intro acc ⟨_, hacc, _, hgt⟩
      simp only [hide, sortedInsert, List.reverse_cons]
      refine ⟨(sorted_append _ _).mpr ⟨hacc, trivial, fun a ha b hb => ?_⟩, fun z => ?_⟩
      · rw [List.mem_singleton] at hb; subst hb
        exact hgt a (List.mem_reverse.mp ha)
      · simp only [List.mem_append, List.mem_reverse, List.mem_singleton, List.not_mem_nil,
          false_or]
        constructor
        · rintro (h | rfl)
          · exact Or.inr h
          · exact Or.inl rfl
        · rintro (rfl | h)
          · exact Or.inr rfl
          · exact Or.inl h
  | cons y ys ih =>
      intro acc ⟨hls, hacc, happ, hgt⟩
      show holSorted _ (sortedInsert x acc (y :: ys)) ∧ _
      unfold sortedInsert
      split
      · next hxy =>
        subst hxy
        refine ⟨happ, fun z => ?_⟩
        simp only [List.mem_append, List.mem_reverse, List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl (Or.inr h))
        · rintro (h | (h | h) | h)
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
      · split
        · next hne hgtxy =>
          refine ⟨(sorted_append _ _).mpr ⟨hacc, (gtSortedEq _ _).mpr ⟨hls, fun b hb => ?_⟩,
            fun a ha b hb => ?_⟩, fun z => ?_⟩
          · rcases List.mem_cons.mp hb with rfl | hb
            · exact hgtxy
            · exact Nat.lt_trans (((gtSortedEq _ _).mp hls).2 b hb) hgtxy
          · have hax := hgt a (List.mem_reverse.mp ha)
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hax
            · rcases List.mem_cons.mp hb with rfl | hb
              · exact Nat.lt_trans hgtxy hax
              · exact Nat.lt_trans (Nat.lt_trans (((gtSortedEq _ _).mp hls).2 b hb) hgtxy) hax
          · simp only [List.mem_append, List.mem_reverse, List.mem_cons]
            constructor
            · rintro (h | h | h | h)
              · exact Or.inr (Or.inr h)
              · exact Or.inl h.symm
              · exact Or.inr (Or.inl (Or.inl h))
              · exact Or.inr (Or.inl (Or.inr h))
            · rintro (h | (h | h) | h)
              · exact Or.inr (Or.inl h.symm)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr h))
              · exact Or.inl h
        · next hne hngt =>
          have hyx : y > x := by omega
          have hyacc : holSorted (· > ·) (y :: acc).reverse := by
            rw [List.reverse_cons]
            have := (sorted_append acc.reverse (y :: ys)).mp happ
            exact (sorted_append _ _).mpr ⟨hacc, trivial, fun a ha b hb => by
              rw [List.mem_singleton] at hb; subst hb
              exact this.2.2 a ha b List.mem_cons_self⟩
          have h := ih (y :: acc) ⟨((gtSortedEq _ _).mp hls).1, hyacc,
            by rw [List.reverse_cons, List.append_assoc]; exact happ,
            fun a ha => by
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hyx
              · exact hgt a ha⟩
          refine ⟨h.1, fun z => ?_⟩
          rw [h.2 z]
          simp only [List.mem_cons]
          constructor
          · rintro (h | h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl (Or.inr h))
            · exact Or.inr (Or.inl (Or.inl h))
            · exact Or.inr (Or.inr h)
          · rintro (h | (h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h))

/-- Exact HOL `sorted_insert_correct` (`reg_allocProofScript.sml:1074-1085`); `x` is
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "sorted_insert_correct"]
theorem sortedInsertCorrect (x : Nat) :
    ∀ (ls : List Nat),
      holSorted (· > ·) ls →
      holSorted (· > ·) (sortedInsert x [] ls) ∧
        ∀ z, z ∈ sortedInsert x [] ls ↔ x = z ∨ z ∈ ls := by
  intro ls hls
  have h := sortedInsertCorrectLem x ls [] ⟨hls, trivial, by simpa using hls, fun _ h => by cases h⟩
  exact ⟨h.1, fun z => by rw [h.2 z]; simp⟩

/-- Exact HOL `sorted_mem_correct` (`reg_allocProofScript.sml:1087-1097`); `x` is free
in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "sorted_mem_correct"]
theorem sortedMemCorrect (x : Nat) :
    ∀ (ls : List Nat), holSorted (· > ·) ls → (sortedMem x ls = true ↔ x ∈ ls) := by
  intro ls
  induction ls with
  | nil => intro _; simp [sortedMem]
  | cons y ys ih =>
      intro hs
      obtain ⟨hys, hgt⟩ := (gtSortedEq y ys).mp hs
      unfold sortedMem
      split
      · next h => subst h; simp
      · split
        · next hne hlt =>
          simp only [Bool.false_eq_true, false_iff, List.mem_cons, not_or]
          refine ⟨hne, fun hm => ?_⟩
          have := hgt x hm
          omega
        · next hne hge =>
          rw [ih hys]
          simp only [List.mem_cons]
          exact ⟨Or.inr, fun h => h.resolve_left hne⟩

/-- The adjacency lists after inserting the edge `x`-`y`. -/
private theorem insertEdge_run (s : State) (x y : Nat) (hx : x < s.adj_ls.length)
    (hy : y < s.adj_ls.length) :
    insertEdge x y s = (.success (), { s with adj_ls :=
      ((s.adj_ls.set x (sortedInsert y [] (holEl x s.adj_ls))).set y
        (sortedInsert x [] (holEl y s.adj_ls))) }) := by
  simp only [insertEdge, Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos hx, if_pos hy,
    ignoreBind, updateAdjLsEqn, List.length_set]

/-- Exact HOL `insert_edge_succeeds` (`reg_allocProofScript.sml:1099-1138`); `s`, `x`
and `y` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "insert_edge_succeeds"]
theorem insertEdgeSucceeds (s : State) (x y : Nat) :
    goodRaState s ∧ y < s.dim ∧ x < s.dim →
    ∃ s', insertEdge x y s = (.success (), s') ∧ goodRaState s' ∧
      s' = { s with adj_ls := s'.adj_ls } ∧
      ∀ a b, (hasEdge s'.adj_ls a b ↔
        (a = x ∧ b = y) ∨ (a = y ∧ b = x) ∨ hasEdge s.adj_ls a b) := by
  intro ⟨hg, hy, hx⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hg
  have hxl : x < s.adj_ls.length := by rw [h1]; exact hx
  have hyl : y < s.adj_ls.length := by rw [h1]; exact hy
  have hmemx : holEl x s.adj_ls ∈ s.adj_ls := by
    rw [holEl_eq_getElem _ _ hxl]; exact List.getElem_mem _
  have hmemy : holEl y s.adj_ls ∈ s.adj_ls := by
    rw [holEl_eq_getElem _ _ hyl]; exact List.getElem_mem _
  obtain ⟨sx, mx⟩ := sortedInsertCorrect y (holEl x s.adj_ls) (h8 _ hmemx)
  obtain ⟨sy, my⟩ := sortedInsertCorrect x (holEl y s.adj_ls) (h8 _ hmemy)
  let adj := (s.adj_ls.set x (sortedInsert y [] (holEl x s.adj_ls))).set y
    (sortedInsert x [] (holEl y s.adj_ls))
  have hlen : adj.length = s.adj_ls.length := by simp [adj]
  have hel : ∀ a, holEl a adj =
      if y = a then sortedInsert x [] (holEl y s.adj_ls)
      else if x = a then sortedInsert y [] (holEl x s.adj_ls) else holEl a s.adj_ls := by
    intro a
    rw [holEl_set _ _ _ _ (by simpa using hyl)]
    split
    · rfl
    · rw [holEl_set _ _ _ _ hxl]
  have hedge : ∀ a b, (hasEdge adj a b ↔
      (a = x ∧ b = y) ∨ (a = y ∧ b = x) ∨ hasEdge s.adj_ls a b) := by
    intro a b
    simp only [hasEdge, hlen, hel]
    by_cases ea : y = a
    · subst ea
      rw [if_pos rfl, my b]
      constructor
      · rintro ⟨ha, hb, rfl | hb'⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨ha, hb, hb'⟩)
      · rintro (⟨rfl, rfl⟩ | ⟨_, rfl⟩ | ⟨ha, hb, hb'⟩)
        · exact ⟨hyl, hyl, Or.inl rfl⟩
        · exact ⟨hyl, hxl, Or.inl rfl⟩
        · exact ⟨ha, hb, Or.inr hb'⟩
    · rw [if_neg ea]
      by_cases eb : x = a
      · subst eb
        rw [if_pos rfl, mx b]
        constructor
        · rintro ⟨ha, hb, rfl | hb'⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr ⟨ha, hb, hb'⟩)
        · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨ha, hb, hb'⟩)
          · exact ⟨hxl, hyl, Or.inl rfl⟩
          · exact absurd h.symm ea
          · exact ⟨ha, hb, Or.inr hb'⟩
      · rw [if_neg eb]
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
          · exact absurd h.symm eb
          · exact absurd h.symm ea
          · exact h
  refine ⟨{ s with adj_ls := adj }, insertEdge_run s x y hxl hyl, ?_, rfl, hedge⟩
  refine ⟨by rw [hlen]; exact h1, h2, h3, h4, h5, h6, ?_, ?_, h9, h10, h11, h12, h13, ?_⟩
  · intro ls hls v hv
    rcases List.mem_or_eq_of_mem_set hls with hls | rfl
    · rcases List.mem_or_eq_of_mem_set hls with hls | rfl
      · exact h7 ls hls v hv
      · rcases (mx v).mp hv with rfl | hv
        · exact hy
        · exact h7 _ hmemx v hv
    · rcases (my v).mp hv with rfl | hv
      · exact hx
      · exact h7 _ hmemy v hv
  · intro ls hls
    rcases List.mem_or_eq_of_mem_set hls with hls | rfl
    · rcases List.mem_or_eq_of_mem_set hls with hls | rfl
      · exact h8 ls hls
      · exact sx
    · exact sy
  · intro a b hab
    rcases (hedge a b).mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact (hedge _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact (hedge _ _).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact (hedge _ _).mpr (Or.inr (Or.inr (h14 a b h)))

/-- Exact HOL `list_insert_edge_succeeds` (`reg_allocProofScript.sml:1140-1166`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "list_insert_edge_succeeds"]
theorem listInsertEdgeSucceeds :
    ∀ (ys : List Nat) (x : Nat) (s : State),
      goodRaState s ∧ x < s.dim ∧ (∀ y ∈ ys, y < s.dim) →
      ∃ s', listInsertEdge x ys s = (.success (), s') ∧ goodRaState s' ∧
        s' = { s with adj_ls := s'.adj_ls } ∧
        ∀ a b, (hasEdge s'.adj_ls a b ↔
          (a = x ∧ b ∈ ys) ∨ (b = x ∧ a ∈ ys) ∨ hasEdge s.adj_ls a b) := by
  intro ys
  induction ys with
  | nil =>
      intro x s ⟨hg, _, _⟩
      exact ⟨s, rfl, hg, rfl, fun a b => by simp⟩
  | cons y ys ih =>
      intro x s ⟨hg, hx, hys⟩
      obtain ⟨s1, hrun1, hg1, hs1, he1⟩ :=
        insertEdgeSucceeds s x y ⟨hg, hys y List.mem_cons_self, hx⟩
      obtain ⟨A, rfl⟩ : ∃ A, s1 = { s with adj_ls := A } := ⟨_, hs1⟩
      obtain ⟨s2, hrun2, hg2, hs2, he2⟩ := ih x { s with adj_ls := A }
        ⟨hg1, hx, fun v hv => hys v (List.mem_cons_of_mem _ hv)⟩
      obtain ⟨B, rfl⟩ : ∃ B, s2 = { s with adj_ls := B } := ⟨_, hs2⟩
      refine ⟨{ s with adj_ls := B }, ?_, hg2, rfl, fun a b => ?_⟩
      · simp only [listInsertEdge, ignoreBind, hrun1]
        exact hrun2
      · rw [he2 a b, he1 a b]
        simp only [List.mem_cons]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩ | h))
          · exact Or.inl ⟨h1, Or.inr h2⟩
          · exact Or.inr (Or.inl ⟨h1, Or.inr h2⟩)
          · exact Or.inl ⟨h1, Or.inl h2⟩
          · exact Or.inr (Or.inl ⟨h2, Or.inl h1⟩)
          · exact Or.inr (Or.inr h)
        · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ | h)
          · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1⟩)))
          · exact Or.inr (Or.inl ⟨h1, h2⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Flapjack.RegAlloc
