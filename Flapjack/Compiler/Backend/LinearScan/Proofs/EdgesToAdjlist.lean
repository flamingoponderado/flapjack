import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Sorting
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange
import Flapjack.Misc.ListEl
import Flapjack.Misc.MiscThe
import Flapjack.Misc.Pair

/-!
# linear_scanProof: forced-edge adjacency lists

Ports of `linear_scanProofScript.sml:2947-3071`: the pure step of
`edges_to_adjlist`, its fold form, the four `forbidden_is_from_*` predicates,
and the characterisation of the adjacency list built from the forced edges.
HOL `EL` is the exact `holEl`, `LEX` the exact `holLex`, `the` the exact
`miscThe`, `insert`/`lookup` are `sptInsert`/`sptLookup`, `FOLDL`/`FOLDR` are
`List.foldl`/`List.foldr`, `MEM` is list membership, `EVERY (\r1,r2. P) l` is
`∀ x, x ∈ l → P` over `x.1`, `x.2`, and `x IN domain t` is `sptDomain t x`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `edges_to_adjlist_step` (`linear_scanProofScript.sml:2947-2955`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "edges_to_adjlist_step_def"]
noncomputable def edgesToAdjlistStep (sth : LinearScanHiddenState) :
    Nat × Nat → Spt (List Nat) → Spt (List Nat)
  | (a, b), acc =>
      if a = b then acc
      else if holLex (· < ·) (· ≤ ·) (holEl a sth.int_beg, a) (holEl b sth.int_beg, b) then
        sptInsert b (a :: miscThe [] (sptLookup b acc)) acc
      else sptInsert a (b :: miscThe [] (sptLookup a acc)) acc

/-- Exact HOL `edges_to_adjlist_FOLDL` (`linear_scanProofScript.sml:2957-2970`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "edges_to_adjlist_FOLDL"]
theorem edgesToAdjlistFoldl :
    ∀ (forced : List (Nat × Nat)) (sth : LinearScanHiddenState) (acc : Spt (List Nat)),
      (∀ x, x ∈ forced → x.1 < sth.int_beg.length ∧ x.2 < sth.int_beg.length) →
      edgesToAdjlist forced acc sth =
        (.success (forced.foldl (fun acc pair => edgesToAdjlistStep sth pair acc) acc),
          sth) := by
  intro forced sth
  induction forced with
  | nil => intro acc _; rw [edgesToAdjlist]; rfl
  | cons p t ih =>
      intro acc hb
      obtain ⟨a, b⟩ := p
      have hab := hb (a, b) List.mem_cons_self
      have ht : ∀ x, x ∈ t → x.1 < sth.int_beg.length ∧ x.2 < sth.int_beg.length :=
        fun x hx => hb x (List.mem_cons_of_mem _ hx)
      rw [edgesToAdjlist, List.foldl_cons]
      by_cases e : a = b
      · rw [if_pos e, ih acc ht]
        simp only [edgesToAdjlistStep, if_pos e]
      · rw [if_neg e]
        simp only [Translator.Monadic.MonadBase.bind, intBegSubEqn, if_pos hab.1, if_pos hab.2]
        have hstep : edgesToAdjlistStep sth (a, b) acc =
            if holEl a sth.int_beg < holEl b sth.int_beg ∨
                (holEl a sth.int_beg = holEl b sth.int_beg ∧ a ≤ b) then
              sptInsert b (a :: miscThe [] (sptLookup b acc)) acc
            else sptInsert a (b :: miscThe [] (sptLookup a acc)) acc := by
          simp only [edgesToAdjlistStep, if_neg e, holLex]; rfl
        rw [hstep]
        split <;> exact ih _ ht

/-- Exact HOL `forbidden_is_from_forced` (`linear_scanProofScript.sml:2972-2976`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forbidden_is_from_forced_def"]
def forbiddenIsFromForced (forced : List (Nat × Nat)) (int_beg : List Int) (reg : Nat)
    (forbidden : List Nat) : Prop :=
  ∀ reg2, (reg ≠ reg2 ∧ ((reg2, reg) ∈ forced ∨ (reg, reg2) ∈ forced) ∧
    holLex (· < ·) (· ≤ ·) (holEl reg2 int_beg, reg2) (holEl reg int_beg, reg)) ↔
      reg2 ∈ forbidden

/-- Exact HOL `forbidden_is_from_forced_sublist`
(`linear_scanProofScript.sml:2978-2982`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forbidden_is_from_forced_sublist_def"]
def forbiddenIsFromForcedSublist (l : List Nat) (forced : List (Nat × Nat))
    (int_beg : List Int) (reg : Nat) (forbidden : List Nat) : Prop :=
  ∀ reg2, (reg ≠ reg2 ∧ ((reg2, reg) ∈ forced ∨ (reg, reg2) ∈ forced) ∧
    holLex (· < ·) (· ≤ ·) (holEl reg2 int_beg, reg2) (holEl reg int_beg, reg)) ↔
      (reg2 ∈ forbidden ∧ reg ∈ l)

/-- Exact HOL `forbidden_is_from_forced_list` (`linear_scanProofScript.sml:2984-2989`);
polymorphic as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forbidden_is_from_forced_list_def"]
def forbiddenIsFromForcedList {α : Type} (forced : List (α × α)) (l : List α) (reg : α)
    (forbidden : List α) : Prop :=
  ∀ reg2, reg2 ∈ l ∧ ((reg2, reg) ∈ forced ∨ (reg, reg2) ∈ forced) → reg2 ∈ forbidden

/-- Exact HOL `forbidden_is_from_map_color_forced`
(`linear_scanProofScript.sml:2991-2996`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forbidden_is_from_map_color_forced_def"]
def forbiddenIsFromMapColorForced (forced : List (Nat × Nat)) (l colors : List Nat)
    (reg : Nat) (forbidden : NumSet) : Prop :=
  ∀ reg2, reg2 ∈ l ∧ ((reg2, reg) ∈ forced ∨ (reg, reg2) ∈ forced) →
    sptDomain forbidden (holEl reg2 colors)

/-- Membership in a looked-up adjacency list after one step. -/
private theorem mem_step (sth : LinearScanHiddenState) (a b reg reg2 : Nat)
    (acc : Spt (List Nat)) :
    reg2 ∈ miscThe [] (sptLookup reg (edgesToAdjlistStep sth (a, b) acc)) ↔
      reg2 ∈ miscThe [] (sptLookup reg acc) ∨
        (a ≠ b ∧
          ((holLex (· < ·) (· ≤ ·) (holEl a sth.int_beg, a) (holEl b sth.int_beg, b) ∧
              reg = b ∧ reg2 = a) ∨
            (¬ holLex (· < ·) (· ≤ ·) (holEl a sth.int_beg, a) (holEl b sth.int_beg, b) ∧
              reg = a ∧ reg2 = b))) := by
  simp only [edgesToAdjlistStep]
  by_cases e : a = b
  · simp [e]
  · rw [if_neg e]
    split
    · next hl =>
      by_cases hr : reg = b
      · subst hr
        rw [sptLookup_sptInsert_same]
        simp only [miscThe, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inr ⟨e, Or.inl ⟨hl, by simp, h⟩⟩
          · exact Or.inl h
        · rintro (h | ⟨_, (⟨_, _, h⟩ | ⟨hn, _, _⟩)⟩)
          · exact Or.inr h
          · exact Or.inl h
          · exact absurd hl hn
      · rw [sptLookup_sptInsert_ne _ _ _ _ hr]
        constructor
        · exact Or.inl
        · rintro (h | ⟨_, (⟨_, h, _⟩ | ⟨hn, _, _⟩)⟩)
          · exact h
          · exact absurd h hr
          · exact absurd hl hn
    · next hl =>
      by_cases hr : reg = a
      · subst hr
        rw [sptLookup_sptInsert_same]
        simp only [miscThe, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inr ⟨e, Or.inr ⟨hl, by simp, h⟩⟩
          · exact Or.inl h
        · rintro (h | ⟨_, (⟨hn, _, _⟩ | ⟨_, _, h⟩)⟩)
          · exact Or.inr h
          · exact absurd hn hl
          · exact Or.inl h
      · rw [sptLookup_sptInsert_ne _ _ _ _ hr]
        constructor
        · exact Or.inl
        · rintro (h | ⟨_, (⟨hn, _, _⟩ | ⟨_, h, _⟩)⟩)
          · exact h
          · exact absurd hn hl
          · exact absurd h hr

/-- Exact HOL `edges_to_adjlist_FOLDR_output` (`linear_scanProofScript.sml:2998-3060`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "edges_to_adjlist_FOLDR_output"]
theorem edgesToAdjlistFoldrOutput :
    ∀ (forced : List (Nat × Nat)) (sth : LinearScanHiddenState),
      ∀ reg, forbiddenIsFromForced forced sth.int_beg reg
        (miscThe [] (sptLookup reg
          (forced.foldr (fun pair acc => edgesToAdjlistStep sth pair acc) .ln))) := by
  intro forced sth
  induction forced with
  | nil =>
      intro reg reg2
      simp [miscThe]
  | cons p t ih =>
      intro reg reg2
      obtain ⟨a, b⟩ := p
      rw [List.foldr_cons, mem_step, ← ih reg reg2]
      simp only [holLex, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ⟨hne, (h | h) | (h | h), hl⟩
        · obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨Ne.symm hne, Or.inl ⟨hl, rfl, rfl⟩⟩
        · exact Or.inl ⟨hne, Or.inl h, hl⟩
        · obtain ⟨rfl, rfl⟩ := h
          refine Or.inr ⟨hne, Or.inr ⟨?_, rfl, rfl⟩⟩
          intro hl'
          apply hne
          omega
        · exact Or.inl ⟨hne, Or.inr h, hl⟩
      · rintro (⟨hne, (h | h), hl⟩ | ⟨hab, (⟨hl, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩)⟩)
        · exact ⟨hne, Or.inl (Or.inr h), hl⟩
        · exact ⟨hne, Or.inr (Or.inr h), hl⟩
        · exact ⟨Ne.symm hab, Or.inl (Or.inl ⟨rfl, rfl⟩), hl⟩
        · refine ⟨hab, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
          omega

/-- Exact HOL `edges_to_adjlist_output` (`linear_scanProofScript.sml:3062-3071`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "edges_to_adjlist_output"]
theorem edgesToAdjlistOutput :
    ∀ (forced : List (Nat × Nat)) (sth : LinearScanHiddenState),
      (∀ x, x ∈ forced → x.1 < sth.int_beg.length ∧ x.2 < sth.int_beg.length) →
      ∃ adjlist, edgesToAdjlist forced .ln sth = (.success adjlist, sth) ∧
        ∀ reg, forbiddenIsFromForced forced sth.int_beg reg
          (miscThe [] (sptLookup reg adjlist)) := by
  intro forced sth hb
  refine ⟨_, edgesToAdjlistFoldl forced sth .ln hb, fun reg reg2 => ?_⟩
  rw [List.foldl_eq_foldr_reverse, ← edgesToAdjlistFoldrOutput forced.reverse sth reg reg2]
  simp only [List.mem_reverse]

end Flapjack.LinearScan
