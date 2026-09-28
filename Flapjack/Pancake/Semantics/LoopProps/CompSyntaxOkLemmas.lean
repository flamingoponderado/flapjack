import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOk
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain

/-!
# loopProps `comp_syntax_ok` lemmas

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`comp_syn_ok_seq2` (739), `comp_syn_ok_nested_seq` (748),
`comp_syn_ok_nested_seq2` (757), `cut_sets_union_domain_subset` (810),
`cut_sets_union_domain_union` (820), `comp_syn_impl_cut_sets_subspt` (831) and
`comp_syn_cut_sets_mem_domain` (841) over the exact `compSyntaxOkHOL`,
`cutSetsHOL` and `holLoopNestedSeq` (bead `flapjack-pxgp.16`).  HOL's `bool`
`comp_syntax_ok` is `compSyntaxOkHOL … = true`; `domain` is `sptDomain`/`sptMem`.
-/

namespace Flapjack

variable {width : Nat} [NeZero width]

theorem holPropBool_eq_true (p : Prop) : holPropBool p = true ↔ p := by
  unfold holPropBool; by_cases h : p <;> simp [h]

theorem sptMem_sptInsert_of (k key : Nat) (v : α) (t : Spt α) (h : sptMem k t) :
    sptMem k (sptInsert key v t) := by
  unfold sptMem sptDomain at *
  rw [sptLookup_sptInsert]; split <;> simp_all

theorem sptMem_sptListInsert_of (k : Nat) (keys : List Nat) (t : NumSet) (h : sptMem k t) :
    sptMem k (sptListInsert keys t) := sptListInsert_mono k keys t h

/-- Exact HOL `comp_syn_ok_seq2` (`loopPropsScript.sml:739-741`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_seq2"
  (words_as_type_indexed_bitvec)]
theorem comp_syn_ok_seq2 :
    ∀ (l : NumSet) (p q : HolLoopProg width),
      compSyntaxOkHOL l p = true ∧ compSyntaxOkHOL (cutSetsHOL l p) q = true →
      compSyntaxOkHOL l (.seq p q) = true := by
  intro l p q ⟨hp, hq⟩
  rw [compSyntaxOkHOL]; simp [hp, hq]

/-- Exact HOL `comp_syn_ok_nested_seq` (`loopPropsScript.sml:748-751`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_nested_seq"
  (words_as_type_indexed_bitvec)]
theorem comp_syn_ok_nested_seq :
    ∀ (p q : List (HolLoopProg width)) (l : NumSet),
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧
      compSyntaxOkHOL (cutSetsHOL l (holLoopNestedSeq p)) (holLoopNestedSeq q) = true →
      compSyntaxOkHOL l (holLoopNestedSeq (p ++ q)) = true
  | [], q, l, ⟨_, hq⟩ => by simpa [holLoopNestedSeq, cutSetsHOL] using hq
  | c :: p, q, l, ⟨hp, hq⟩ => by
      simp only [List.cons_append, holLoopNestedSeq]
      rw [holLoopNestedSeq] at hp
      rw [compSyntaxOkHOL, Bool.and_eq_true] at hp ⊢
      refine ⟨hp.1, comp_syn_ok_nested_seq p q (cutSetsHOL l c) ⟨hp.2, ?_⟩⟩
      simpa [holLoopNestedSeq, cutSetsHOL] using hq

/-- Exact HOL `comp_syn_ok_nested_seq2` (`loopPropsScript.sml:757-760`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_nested_seq2"
  (words_as_type_indexed_bitvec)]
theorem comp_syn_ok_nested_seq2 :
    ∀ (p q : List (HolLoopProg width)) (l : NumSet),
      compSyntaxOkHOL l (holLoopNestedSeq (p ++ q)) = true →
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧
      compSyntaxOkHOL (cutSetsHOL l (holLoopNestedSeq p)) (holLoopNestedSeq q) = true
  | [], q, l, h => by
      refine ⟨by simp [holLoopNestedSeq, compSyntaxOkHOL], ?_⟩
      simpa [holLoopNestedSeq, cutSetsHOL] using h
  | c :: p, q, l, h => by
      simp only [List.cons_append, holLoopNestedSeq] at h
      rw [compSyntaxOkHOL, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := comp_syn_ok_nested_seq2 p q (cutSetsHOL l c) h.2
      refine ⟨?_, ?_⟩
      · rw [holLoopNestedSeq, compSyntaxOkHOL, Bool.and_eq_true]; exact ⟨h.1, h1⟩
      · simpa [holLoopNestedSeq, cutSetsHOL] using h2

theorem compSyntaxOk_cut_sets_mono :
    ∀ (p : HolLoopProg width) (l : NumSet), compSyntaxOkHOL l p = true →
      ∀ k, sptMem k l → sptMem k (cutSetsHOL l p)
  | .skip, l, _, k, hk | .break _, l, _, k, hk => by simpa [cutSetsHOL] using hk
  | .assign _ _, l, _, k, hk | .locValue _ _, l, _, k, hk | .load32 _ _, l, _, k, hk
  | .loadByte _ _, l, _, k, hk => by
      simp only [cutSetsHOL]; exact sptMem_sptInsert_of _ _ _ _ hk
  | .arith op, l, _, k, hk => by
      cases op <;> simp only [cutSetsHOL] <;>
        first
          | exact sptMem_sptInsert_of _ _ _ _ hk
          | exact sptMem_sptInsert_of _ _ _ _ (sptMem_sptInsert_of _ _ _ _ hk)
  | .loop _ _ _, l, _, k, hk => by simpa [cutSetsHOL] using hk
  | .seq p q, l, h, k, hk => by
      rw [compSyntaxOkHOL, Bool.and_eq_true] at h
      simp only [cutSetsHOL]
      exact compSyntaxOk_cut_sets_mono q _ h.2 k (compSyntaxOk_cut_sets_mono p l h.1 k hk)
  | .ite _ _ _ _ _ nl, l, h, k, hk => by
      rw [compSyntaxOkHOL, Bool.and_eq_true, holPropBool_eq_true] at h
      obtain ⟨names, rfl⟩ := h.2
      simp only [cutSetsHOL]; exact sptMem_sptListInsert_of _ _ _ hk
  | .primitive _ _ _, _, h, _, _ | .store _ _, _, h, _, _ | .setGlobal _ _, _, h, _, _
  | .store32 _ _, _, h, _, _ | .storeByte _ _, _, h, _, _ | .continue _, _, h, _, _
  | .raise _, _, h, _, _ | .return _, _, h, _, _ | .shMem _ _ _, _, h, _, _
  | .tick, _, h, _, _ | .mark _, _, h, _, _ | .fail, _, h, _, _
  | .call _ _ _ _, _, h, _, _ | .ffi _ _ _ _ _ _, _, h, _, _ => by
      simp [compSyntaxOkHOL] at h
termination_by p => sizeOf p

/-- Exact HOL `cut_sets_union_domain_subset` (`loopPropsScript.sml:810-812`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_union_domain_subset"
  (words_as_type_indexed_bitvec)]
theorem cut_sets_union_domain_subset :
    ∀ (p : HolLoopProg width) (l : NumSet), compSyntaxOkHOL l p = true →
      ∀ k, sptDomain l k → sptDomain (cutSetsHOL l p) k :=
  fun p l h k hk => compSyntaxOk_cut_sets_mono p l h k hk

/-- Exact HOL `cut_sets_union_domain_union` (`loopPropsScript.sml:820-822`):
    `?l'. domain (cut_sets l p) = domain l ∪ domain l'`; set union as the
    pointwise disjunction of the `sptDomain` predicates. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_union_domain_union"
  (words_as_type_indexed_bitvec)]
theorem cut_sets_union_domain_union :
    ∀ (p : HolLoopProg width) (l : NumSet), compSyntaxOkHOL l p = true →
      ∃ l' : NumSet, sptDomain (cutSetsHOL l p) = fun k => sptDomain l k ∨ sptDomain l' k := by
  intro p l h
  refine ⟨cutSetsHOL l p, ?_⟩
  funext k
  apply propext
  constructor
  · intro hk; exact Or.inr hk
  · intro hk; rcases hk with hk | hk
    · exact compSyntaxOk_cut_sets_mono p l h k hk
    · exact hk

/-- Exact HOL `comp_syn_cut_sets_mem_domain` (`loopPropsScript.sml:841-844`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_cut_sets_mem_domain"
  (words_as_type_indexed_bitvec)]
theorem comp_syn_cut_sets_mem_domain :
    ∀ (p : HolLoopProg width) (l : NumSet) (n : Nat),
      compSyntaxOkHOL l p = true ∧ sptMem n l → sptMem n (cutSetsHOL l p) :=
  fun p l n ⟨h, hn⟩ => compSyntaxOk_cut_sets_mono p l h n hn

/-- Exact HOL `comp_syn_impl_cut_sets_subspt` (`loopPropsScript.sml:831-833`):
    `comp_syntax_ok l p ==> subspt l (cut_sets l p)`, with `subspt` the reviewed
    `sptSubspt`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_impl_cut_sets_subspt"
  (words_as_type_indexed_bitvec)]
theorem comp_syn_impl_cut_sets_subspt :
    ∀ (p : HolLoopProg width) (l : NumSet), compSyntaxOkHOL l p = true →
      sptSubspt l (cutSetsHOL l p) := by
  intro p l h k hk
  have hk2 := compSyntaxOk_cut_sets_mono p l h k hk
  refine ⟨hk2, ?_⟩
  unfold sptMem sptDomain at hk hk2
  cases h1 : sptLookup k (cutSetsHOL l p) <;> cases h2 : sptLookup k l <;> simp_all

end Flapjack
