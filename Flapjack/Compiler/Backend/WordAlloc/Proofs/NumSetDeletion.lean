import Flapjack.Compiler.Backend.WordAlloc.Proofs.NumSets
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ScopedInjection
import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.Sptree.Wf
import Flapjack.Misc.SptreeLookup

/-!
# Word allocation numeric-set union and deletion lemmas

Counterparts of the local `word_allocProofScript.sml:2685-2811` lemmas used by
`clash_tree_colouring_ok`: insertion as a union, list insertion as a union of
well-formed trees, commuting deletions, list deletion as a fold, the
well-formedness of expression liveness, and the image of a difference.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- Exact HOL `domain_insert_eq_union` (`word_allocProofScript.sml:2685-2690`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_insert_eq_union"]
theorem domainInsertEqUnion (num : Nat) (live : NumSet) :
    sptDomain (sptInsert num () live) = sptDomain (sptUnion (sptInsert num () .ln) live) := by
  rw [sptDomain_sptUnion]
  funext k
  apply propext
  unfold sptDomain
  by_cases h : k = num
  · subst h; simp [sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne num k () _ h, sptLookup_sptInsert_ne num k () _ h]
    simp [sptLookup]

/-- List insertion preserves well-formedness (Flapjack infrastructure; HOL
uses `wf_insert` inline). -/
theorem sptWf_numsetListInsert (t : NumSet) (ht : sptWf t = true) :
    ∀ ls : List Nat, sptWf (numsetListInsert ls t) = true
  | [] => ht
  | x :: xs => sptWfInsert x () _ (sptWf_numsetListInsert t ht xs)

/-- Exact HOL `numset_list_insert_eq_UNION` (`word_allocProofScript.sml:2729-2749`):
inserting a list into a well-formed tree is the union with any well-formed tree
whose domain is the list's member set. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_insert_eq_UNION"]
theorem numsetListInsertEqUnion :
    ∀ (t t' : NumSet) (ls : List Nat),
      sptWf t = true ∧ sptWf t' = true ∧ sptDomain t' = (fun k => k ∈ ls) →
      numsetListInsert ls t = sptUnion t' t := by
  rintro t t' ls ⟨ht, ht', hd⟩
  rw [sptEqThm _ _ ⟨sptWf_numsetListInsert t ht ls, sptWfUnion t' t ⟨ht', ht⟩⟩]
  intro n
  rw [lookupNumsetListInsert, sptLookup_sptUnion]
  have hn := congrFun hd n
  unfold sptDomain at hn
  by_cases hm : n ∈ ls
  · rw [if_pos hm]
    have hs : (sptLookup n t').isSome = true := by rw [hn]; exact hm
    cases h : sptLookup n t' with
    | none => rw [h] at hs; cases hs
    | some u => rfl
  · rw [if_neg hm]
    have hs : (sptLookup n t').isSome = false := by
      cases h : (sptLookup n t').isSome
      · rfl
      · rw [h] at hn; exact absurd (hn ▸ rfl) hm
    cases h : sptLookup n t' with
    | none => rfl
    | some u => rw [h] at hs; cases hs

/-- Exact HOL `wf_delete_swap` (`word_allocProofScript.sml:2751-2760`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_delete_swap"]
theorem wfDeleteSwap {α : Type} (t : Spt α) (a c : Nat) (ht : sptWf t = true) :
    sptDelete a (sptDelete c t) = sptDelete c (sptDelete a t) := by
  rw [sptEqThm _ _ ⟨sptWfDelete _ a (sptWfDelete t c ht), sptWfDelete _ c (sptWfDelete t a ht)⟩]
  intro n
  rw [sptLookup_sptDelete, sptLookup_sptDelete, sptLookup_sptDelete, sptLookup_sptDelete]
  by_cases h1 : n = a <;> by_cases h2 : n = c <;> simp [h1, h2]

/-- Exact HOL `numset_list_delete_swap` (`word_allocProofScript.sml:2762-2772`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "numset_list_delete_swap"]
theorem numsetListDeleteSwap {α : Type} :
    ∀ (ls : List Nat) (h : Nat) (live : Spt α), sptWf live = true →
      sptWf (numsetListDelete ls live) = true ∧
        numsetListDelete ls (sptDelete h live) = sptDelete h (numsetListDelete ls live)
  | [], _, _, hw => ⟨hw, rfl⟩
  | x :: xs, h, live, hw => by
      simp only [numsetListDelete]
      have ih1 := numsetListDeleteSwap xs h (sptDelete x live) (sptWfDelete live x hw)
      refine ⟨ih1.1, ?_⟩
      rw [wfDeleteSwap live x h hw]
      exact ih1.2

/-- Exact HOL `wf_numset_list_delete_eq` (`word_allocProofScript.sml:2774-2780`):
on a well-formed tree the right fold of deletions is `numset_list_delete`. HOL's
universally quantified `live` does not occur in the statement (its type is an
unconstrained variable), so it is omitted. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_numset_list_delete_eq"]
theorem wfNumsetListDeleteEq {α : Type} :
    ∀ (ls : List Nat) (t : Spt α), sptWf t = true →
      ls.foldr sptDelete t = numsetListDelete ls t
  | [], _, _ => rfl
  | x :: xs, t, ht => by
      rw [List.foldr_cons, wfNumsetListDeleteEq xs t ht, numsetListDelete,
        (numsetListDeleteSwap xs x t ht).2]

/-- `big_union` of well-formed trees is well formed (Flapjack infrastructure;
HOL unfolds `big_union_def` with `wf_union` inline). -/
theorem sptWf_bigUnion : ∀ (sets : List (Spt Unit)), (∀ s, s ∈ sets → sptWf s = true) →
    sptWf (bigUnion sets) = true
  | [], _ => rfl
  | s :: ss, h => by
      unfold bigUnion
      rw [List.foldr_cons]
      exact sptWfUnion _ _ ⟨h s List.mem_cons_self,
        sptWf_bigUnion ss (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- Exact HOL `wf_get_live_exp` (`word_allocProofScript.sml:2782-2789`). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "wf_get_live_exp"
  (words_as_type_indexed_bitvec)]
theorem wfGetLiveExp {width : Nat} [NeZero width] :
    ∀ exp : WordLangExpHOL (BitVec width), sptWf (getLiveExp exp) = true
  | .var n => by rw [getLiveExp]; exact sptWfInsert n () _ rfl
  | .load e => by rw [getLiveExp]; exact wfGetLiveExp e
  | .op _ es => by
      rw [getLiveExp]
      refine sptWf_bigUnion _ (fun s hs => ?_)
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
      exact wfGetLiveExp e
  | .shift _ e n => by
      rw [getLiveExp]
      exact sptWfUnion _ _ ⟨wfGetLiveExp e, wfGetLiveExp n⟩
  | .const _ => by rw [getLiveExp]; rfl
  | .lookup _ => by rw [getLiveExp]; rfl
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | decreasing_trivial
    | (have := List.sizeOf_lt_of_mem he; simp_wf; omega)

/-- Exact HOL `IMAGE_DIFF` (`word_allocProofScript.sml:2806-2811`): under
injectivity on `s ∪ t`, the image of `s DIFF t` is the difference of the
images. HOL sets are predicates, `IMAGE` an existential and `DIFF` a negated
conjunct, as in the accepted `INJ_IMP_IMAGE_DIFF` port. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "IMAGE_DIFF"]
theorem imageDiff {α β : Type} (f : α → β) (s t : α → Prop)
    (h : ∀ x y, (s x ∨ t x) → (s y ∨ t y) → f x = f y → x = y) :
    (fun y => ∃ x, (s x ∧ ¬ t x) ∧ f x = y) =
      (fun y => (∃ x, s x ∧ f x = y) ∧ ¬ (∃ x, t x ∧ f x = y)) :=
  injImageDiff f s t h

end Flapjack.WordAlloc
