import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapExtend
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapPreservation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveDomains
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

/-!
# word_allocProof merge/fake-move frames and `force_rename` lemmas

Ports of `word_allocProofScript.sml` frame facts for the native SSA branch
reconciliation (`fake_moves_frame`, `fake_moves_frame2`, `fake_moves_frame3`;
`merge_moves_frame3` is Sol-C's delivered port, bead wma3) and of the `force_rename` lemmas. HOL `domain` is the
predicate `sptDomain`, `set ls` list membership, `∪`/`∩` disjunction and
conjunction, and HOL `let (a, b, c, d, e) = f ... in` projections of the
result. `prio` (free in the HOL statements) and the program word width are
universally quantified.
-/

namespace Flapjack.Compiler.Backend.WordAlloc

private theorem inter_iff {α β : Type} (a : Spt α) (b : Spt β) (x : Nat) :
    sptDomain (sptInter a b) x ↔ sptDomain a x ∧ sptDomain b x := by
  rw [sptDomain_sptInter]

private theorem dom_iff {α : Type} (a : Spt α) (x : Nat) :
    sptDomain a x ↔ ∃ v, sptLookup x a = some v := by
  unfold sptDomain; cases sptLookup x a <;> simp

private theorem lookup_ins {α : Type} (x k : Nat) (v : α) (t : Spt α) :
    sptLookup x (sptInsert k v t) = if x = k then some v else sptLookup x t := by
  by_cases h : x = k
  · subst h; simp [sptLookup_sptInsert_same]
  · simp [h, sptLookup_sptInsert_ne k x v t h]

/-- HOL `fake_moves_frame3` (`word_allocProofScript.sml:4968-4993`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame3"
  (words_as_type_indexed_bitvec)]
theorem fakeMovesFrame3 {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (ls : List Nat) (na : Nat) (ssaL ssaR : Spt Nat),
      ∀ x, ¬ x ∈ ls ∨ sptDomain (sptInter ssaL ssaR) x →
        sptLookup x (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.1 = sptLookup x ssaL ∧ sptLookup x (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.2 = sptLookup x ssaR := by
  intro ls
  induction ls with
  | nil => intro na ssaL ssaR x _; simp [fakeMoves]
  | cons y ys ih =>
      intro na ssaL ssaR x hx
      have ih' := ih na ssaL ssaR
      generalize h : fakeMoves (width := width) prio ys ssaL ssaR na = res at ih'
      obtain ⟨sl, sr, na', l', r'⟩ := res
      try dsimp only at ih'
      try dsimp only at f3
      have hx' : ¬ x ∈ ys ∨ sptDomain (sptInter ssaL ssaR) x := by
        rcases hx with hx | hx
        · exact Or.inl (fun hm => hx (List.mem_cons_of_mem _ hm))
        · exact Or.inr hx
      obtain ⟨hl, hr⟩ := ih' x hx'
      simp only [fakeMoves, h]
      -- the inserting cases touch only `y`; at `y` itself both lookups are unchanged
      have hy : x = y → (sptLookup y l' = sptLookup y ssaL ∧ sptLookup y r' = sptLookup y ssaR) ∧
          sptDomain (sptInter ssaL ssaR) y := by
        rintro rfl
        rcases hx with hx | hx
        · exact absurd (List.mem_cons_self ..) hx
        · exact ⟨⟨hl, hr⟩, hx⟩
      split
      · rename_i ly hnone hsome
        have hne : x ≠ y := by
          intro he
          obtain ⟨⟨hl0, _⟩, hd⟩ := hy he
          rw [inter_iff, dom_iff] at hd
          obtain ⟨⟨v, hv⟩, _⟩ := hd
          rw [hl0, hv] at hnone; cases hnone
        simp only [lookup_ins, hne, if_false]; exact ⟨hl, hr⟩
      · rename_i lx hsome hnone
        have hne : x ≠ y := by
          intro he
          obtain ⟨⟨_, hr0⟩, hd⟩ := hy he
          rw [inter_iff, dom_iff, dom_iff] at hd
          obtain ⟨_, ⟨v, hv⟩⟩ := hd
          rw [hr0, hv] at hnone; cases hnone
        simp only [lookup_ins, hne, if_false]; exact ⟨hl, hr⟩
      · exact ⟨hl, hr⟩

/-- HOL `fake_moves_frame` (`word_allocProofScript.sml:4917-4946`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame"
  (words_as_type_indexed_bitvec)]
theorem fakeMovesFrame {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (ls : List Nat) (na : Nat) (ssaL ssaR : Spt Nat),
      isAllocVar na →
      isAllocVar (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.1 ∧ na ≤ (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.1 ∧
        (ssaMapOK na ssaL → ssaMapOK (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.1 (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.1) ∧
        (ssaMapOK na ssaR → ssaMapOK (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.1 (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.2) := by
  intro ls
  induction ls with
  | nil => intro na ssaL ssaR ha; simp [fakeMoves, ha]
  | cons y ys ih =>
      intro na ssaL ssaR ha
      have ih' := ih na ssaL ssaR ha
      generalize h : fakeMoves (width := width) prio ys ssaL ssaR na = res at ih'
      obtain ⟨sl, sr, na', l', r'⟩ := res
      try dsimp only at ih'
      try dsimp only at f3
      obtain ⟨ha', hle, hokL, hokR⟩ := ih'
      have hphy : ¬ isPhyVar na' := by
        simp only [isAllocVar, decide_eq_true_eq] at ha'
        simp only [isPhyVar, decide_eq_true_eq]; omega
      have ha4 : isAllocVar (na' + 4) := by
        simp only [isAllocVar, decide_eq_true_eq] at ha' ⊢; omega
      simp only [fakeMoves, h]
      split <;> dsimp only
      · exact ⟨ha4, by omega, fun hk => ssaMapOKExtend na' l' y ⟨hokL hk, hphy⟩,
          fun hk => ssaMapOKExtend na' r' y ⟨hokR hk, hphy⟩⟩
      · exact ⟨ha4, by omega, fun hk => ssaMapOKExtend na' l' y ⟨hokL hk, hphy⟩,
          fun hk => ssaMapOKExtend na' r' y ⟨hokR hk, hphy⟩⟩
      · exact ⟨ha', hle, hokL, hokR⟩

/-- HOL `fake_moves_frame2` (`word_allocProofScript.sml:4948-4966`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_frame2"
  (words_as_type_indexed_bitvec)]
theorem fakeMovesFrame2 {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (ls : List Nat) (na : Nat) (ssaL ssaR : Spt Nat),
      sptDomain (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.1 =
          (fun x => sptDomain ssaL x ∨ (x ∈ ls ∧ (sptDomain ssaR x ∨ sptDomain ssaL x))) ∧
        sptDomain (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.2 =
          (fun x => sptDomain ssaR x ∨ (x ∈ ls ∧ (sptDomain ssaR x ∨ sptDomain ssaL x))) ∧
        ∀ x, x ∈ ls ∧ ¬ sptDomain (sptInter ssaL ssaR) x →
          sptLookup x (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.1 = sptLookup x (fakeMoves prio ls ssaL ssaR na : WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat).2.2.2.2 := by
  intro ls
  induction ls with
  | nil => intro na ssaL ssaR; simp [fakeMoves]
  | cons y ys ih =>
      intro na ssaL ssaR
      have ih' := ih na ssaL ssaR
      have f3 := fakeMovesFrame3 (width := width) prio ys na ssaL ssaR
      generalize h : fakeMoves (width := width) prio ys ssaL ssaR na = res at ih' f3
      obtain ⟨sl, sr, na', l', r'⟩ := res
      try dsimp only at ih'
      try dsimp only at f3
      obtain ⟨domL, domR, agree⟩ := ih'
      have memL : ∀ x, sptDomain l' x ↔
          sptDomain ssaL x ∨ (x ∈ ys ∧ (sptDomain ssaR x ∨ sptDomain ssaL x)) := by
        intro x; rw [domL]
      have memR : ∀ x, sptDomain r' x ↔
          sptDomain ssaR x ∨ (x ∈ ys ∧ (sptDomain ssaR x ∨ sptDomain ssaL x)) := by
        intro x; rw [domR]
      have domIns : ∀ (t : Spt Nat) (k v : Nat) (x : Nat),
          sptDomain (sptInsert k v t) x ↔ x = k ∨ sptDomain t x := by
        intro t k v x
        exact sptMem_sptInsert x k v t
      simp only [fakeMoves, h]
      split <;> dsimp only
      · rename_i ly hnone hsome
        have hyR : sptDomain r' y := by rw [dom_iff]; exact ⟨ly, hsome⟩
        have hyRL : sptDomain ssaR y ∨ sptDomain ssaL y := by
          rcases (memR y).mp hyR with h1 | ⟨_, h1⟩
          · exact Or.inl h1
          · exact h1
        refine ⟨?_, ?_, ?_⟩
        · funext x; apply propext; rw [domIns, memL]
          constructor
          · rintro (rfl | h1 | ⟨hm, h2⟩)
            · exact Or.inr ⟨List.mem_cons_self .., hyRL⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact Or.inr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ⟨hm, h2⟩)
        · funext x; apply propext; rw [domIns, memR]
          constructor
          · rintro (rfl | h1 | ⟨hm, h2⟩)
            · exact Or.inr ⟨List.mem_cons_self .., hyRL⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact Or.inr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ⟨hm, h2⟩)
        · rintro x ⟨hm, hni⟩
          by_cases hxy : x = y
          · subst hxy; simp [lookup_ins]
          · simp only [lookup_ins, hxy, if_false]
            exact agree x ⟨(List.mem_cons.mp hm).resolve_left hxy, hni⟩
      · rename_i lx hsome hnone
        have hyL : sptDomain l' y := by rw [dom_iff]; exact ⟨lx, hsome⟩
        have hyRL : sptDomain ssaR y ∨ sptDomain ssaL y := by
          rcases (memL y).mp hyL with h1 | ⟨_, h1⟩
          · exact Or.inr h1
          · exact h1
        refine ⟨?_, ?_, ?_⟩
        · funext x; apply propext; rw [domIns, memL]
          constructor
          · rintro (rfl | h1 | ⟨hm, h2⟩)
            · exact Or.inr ⟨List.mem_cons_self .., hyRL⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact Or.inr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ⟨hm, h2⟩)
        · funext x; apply propext; rw [domIns, memR]
          constructor
          · rintro (rfl | h1 | ⟨hm, h2⟩)
            · exact Or.inr ⟨List.mem_cons_self .., hyRL⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact Or.inr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ⟨hm, h2⟩)
        · rintro x ⟨hm, hni⟩
          by_cases hxy : x = y
          · subst hxy; simp [lookup_ins]
          · simp only [lookup_ins, hxy, if_false]
            exact agree x ⟨(List.mem_cons.mp hm).resolve_left hxy, hni⟩
      · rename_i hcase1 hcase2
        -- both lookups present or both absent at `y`
        have both : (sptDomain l' y ↔ sptDomain r' y) := by
          rw [dom_iff, dom_iff]
          cases hl : sptLookup y l' <;> cases hr : sptLookup y r' <;> simp_all
        refine ⟨?_, ?_, ?_⟩
        · funext x; apply propext
          constructor
          · intro hx; rw [memL] at hx
            rcases hx with h1 | ⟨hm, h2⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact (memL x).mpr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · rcases h2 with h2 | h2
                · exact both.mpr ((memR x).mpr (Or.inl h2))
                · exact (memL x).mpr (Or.inl h2)
              · exact (memL x).mpr (Or.inr ⟨hm, h2⟩)
        · funext x; apply propext
          constructor
          · intro hx; rw [memR] at hx
            rcases hx with h1 | ⟨hm, h2⟩
            · exact Or.inl h1
            · exact Or.inr ⟨List.mem_cons_of_mem _ hm, h2⟩
          · rintro (h1 | ⟨hm, h2⟩)
            · exact (memR x).mpr (Or.inl h1)
            · rcases List.mem_cons.mp hm with rfl | hm
              · rcases h2 with h2 | h2
                · exact (memR x).mpr (Or.inl h2)
                · exact both.mp ((memL x).mpr (Or.inl h2))
              · exact (memR x).mpr (Or.inr ⟨hm, h2⟩)
        · rintro x ⟨hm, hni⟩
          rcases List.mem_cons.mp hm with rfl | hm
          · by_cases hxs : x ∈ ys
            · exact agree x ⟨hxs, hni⟩
            · obtain ⟨e1, e2⟩ := f3 x (Or.inl hxs)
              rw [e1, e2]
              have hlr : (sptLookup x l').isSome = (sptLookup x r').isSome := by
                have := both; simp only [sptDomain] at this
                exact Bool.eq_iff_iff.mpr this
              rw [e1, e2] at hlr
              cases hL : sptLookup x ssaL <;> cases hR : sptLookup x ssaR
              · rfl
              · simp [hL, hR] at hlr
              · simp [hL, hR] at hlr
              · exact absurd (by rw [inter_iff, dom_iff, dom_iff]; exact ⟨⟨_, hL⟩, ⟨_, hR⟩⟩) hni
          · exact agree x ⟨hm, hni⟩

/-- HOL `ssa_map_ok_force_rename` (`word_allocProofScript.sml:5935-5949`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_force_rename"]
theorem ssaMapOKForceRename (na : Nat) :
    ∀ (ls : List (Nat × Nat)) (ssa : Spt Nat),
      ssaMapOK na ssa ∧ (∀ x ∈ ls, x.2 < na ∧ ¬ isPhyVar x.2) →
      ssaMapOK na (forceRename ls ssa) := by
  intro ls
  induction ls with
  | nil => intro ssa h; exact h.1
  | cons p ps ih =>
      intro ssa ⟨hok, hall⟩
      obtain ⟨x, y⟩ := p
      have hy := hall (x, y) (List.mem_cons_self ..)
      exact ih (sptInsert x y ssa)
        ⟨ssaMapOKInsert na ssa x y ⟨hok, hy.1, hy.2⟩,
          fun q hq => hall q (List.mem_cons_of_mem _ hq)⟩

/-- HOL `lookup_force_rename_aux` (`word_allocProofScript.sml:6347-6362`); HOL
`ALOOKUP` is the library rendering `holAlookup`. `x` is free. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_force_rename_aux"]
theorem lookupForceRenameAux {α : Type} (x : Nat) :
    ∀ (ls : List (Nat × α)) (ssa : Spt α),
      sptLookup x (forceRename ls.reverse ssa) =
        match holAlookup ls x with
        | none => sptLookup x ssa
        | some y => some y := by
  intro ls
  induction ls with
  | nil => intro ssa; simp [forceRename, holAlookup]
  | cons p ps ih =>
      intro ssa
      obtain ⟨k, v⟩ := p
      have hsplit : ∀ (us : List (Nat × α)) (s : Spt α),
          forceRename (us ++ [(k, v)]) s = sptInsert k v (forceRename us s) := by
        intro us; induction us with
        | nil => intro s; rfl
        | cons q qs ihq => intro s; obtain ⟨a, b⟩ := q; exact ihq _
      rw [List.reverse_cons, hsplit, lookup_ins, ih]
      by_cases hk : x = k
      · subst hk; simp [holAlookup]
      · simp [holAlookup, hk, Ne.symm hk]

/-- HOL `lookup_force_rename` (`word_allocProofScript.sml:6364-6371`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "lookup_force_rename"]
theorem lookupForceRename {α : Type} (x : Nat) (ls : List (Nat × α)) (ssa : Spt α) :
    sptLookup x (forceRename ls ssa) =
      match holAlookup ls.reverse x with
      | none => sptLookup x ssa
      | some y => some y := by
  have := lookupForceRenameAux x ls.reverse ssa
  rwa [List.reverse_reverse] at this

/-- HOL `domain_force_rename` (`word_allocProofScript.sml:6373-6381`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_force_rename"]
theorem domainForceRename {α : Type} (ls : List (Nat × α)) (ssa : Spt α) :
    sptDomain (forceRename ls ssa) = fun x => sptDomain ssa x ∨ x ∈ ls.map Prod.fst := by
  induction ls generalizing ssa with
  | nil => funext x; simp [forceRename]
  | cons p ps ih =>
      obtain ⟨k, v⟩ := p
      funext x; apply propext
      show sptDomain (forceRename ps (sptInsert k v ssa)) x ↔ _
      rw [ih]
      have : sptDomain (sptInsert k v ssa) x ↔ x = k ∨ sptDomain ssa x := sptMem_sptInsert x k v ssa
      simp only [this, List.map_cons, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

end Flapjack.Compiler.Backend.WordAlloc
