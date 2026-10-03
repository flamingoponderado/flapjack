import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Pancake.WordConvs.ExpressionMonotonicity

namespace Flapjack.WordAlloc

local instance {α : Type} (tree : Spt α) (key : Nat) : Decidable (sptDomain tree key) :=
  inferInstanceAs (Decidable ((sptLookup key tree).isSome = true))

/-- Exact HOL membership-to-domain-subset statement for expression live sets.
HOL set inclusion is rendered pointwise over the characteristic predicates;
the list may contain repeated expressions and the trees need no extra wf premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "domain_big_union_subset"
  (words_as_type_indexed_bitvec)]
theorem domainBigUnionSubset {width : Nat} [NeZero width] :
    ∀ (ls : List (WordLangExpHOL (BitVec width))) (a : WordLangExpHOL (BitVec width)),
      a ∈ ls → ∀ key, sptDomain (getLiveExp a) key →
        sptDomain (bigUnion (ls.map getLiveExp)) key := by
  intro ls
  induction ls with
  | nil =>
      intro a ha
      simp at ha
  | cons head tail ih =>
      intro a ha key hk
      change sptDomain (sptUnion (getLiveExp head) (bigUnion (tail.map getLiveExp))) key
      rw [sptDomain_sptUnion]
      rcases List.mem_cons.mp ha with heq | hmem
      · subst a
        exact Or.inl hk
      · exact Or.inr (ih a hmem key hk)

/-- Flapjack list lifting of the original expression monotonicity theorem;
this has no separate HOL declaration. -/
private theorem expressionListMono {width : Nat} [NeZero width]
    (es : List (WordLangExpHOL (BitVec width))) (P Q : Nat → Bool)
    (image : ∀ x, P x = true → Q x = true)
    (valid : everyVarExpsHOL P es = true) : everyVarExpsHOL Q es = true := by
  induction es with
  | nil => simp [everyVarExpsHOL]
  | cons head tail ih =>
      simp only [everyVarExpsHOL, Bool.and_eq_true] at valid ⊢
      exact ⟨everyVarExpMono P head Q ⟨image, valid.1⟩, ih valid.2⟩

/-- Original unconditional occurrence coverage by the expression live-set
domain, including every operator argument and both Shift operands. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "every_var_exp_get_live_exp" (words_as_type_indexed_bitvec)]
theorem everyVarExp_getLiveExp {width : Nat} [NeZero width]
    (exp : WordLangExpHOL (BitVec width)) :
    everyVarExpHOL (fun x => decide (sptDomain (getLiveExp exp) x)) exp = true := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      everyVarExpHOL (fun x => decide (sptDomain (getLiveExp e) x)) e = true)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      everyVarExpsHOL (fun x => decide (sptDomain (bigUnion (es.map getLiveExp)) x)) es = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ exp
  · intro value; simp [everyVarExpHOL]
  · intro name
    simp only [everyVarExpHOL, getLiveExp, decide_eq_true_eq]
    change sptMem name (sptInsert name () .ln)
    simp [sptMem_sptInsert]
  · intro store; simp [everyVarExpHOL]
  · intro address ih; simpa only [everyVarExpHOL, getLiveExp] using ih
  · intro operator args ih; simpa only [everyVarExpHOL, getLiveExp] using ih
  · intro operator left right ihLeft ihRight
    simp only [everyVarExpHOL, getLiveExp, Bool.and_eq_true]
    constructor
    · apply everyVarExpMono _ left _ ⟨?_, ihLeft⟩
      intro x hx
      simp only [decide_eq_true_eq, sptDomain_sptUnion] at hx ⊢
      exact Or.inl hx
    · apply everyVarExpMono _ right _ ⟨?_, ihRight⟩
      intro x hx
      simp only [decide_eq_true_eq, sptDomain_sptUnion] at hx ⊢
      exact Or.inr hx
  · simp [everyVarExpsHOL]
  · intro head tail ihHead ihTail
    simp only [everyVarExpsHOL, Bool.and_eq_true]
    change everyVarExpHOL (fun x => decide (sptDomain
      (sptUnion (getLiveExp head) (bigUnion (tail.map getLiveExp))) x)) head = true ∧
      everyVarExpsHOL (fun x => decide (sptDomain
      (sptUnion (getLiveExp head) (bigUnion (tail.map getLiveExp))) x)) tail = true
    constructor
    · apply everyVarExpMono _ head _ ⟨?_, ihHead⟩
      intro x hx
      simp only [decide_eq_true_eq, sptDomain_sptUnion] at hx ⊢
      exact Or.inl hx
    · apply expressionListMono tail _ _ ?_ ihTail
      intro x hx
      simp only [decide_eq_true_eq, sptDomain_sptUnion] at hx ⊢
      exact Or.inr hx

end Flapjack.WordAlloc
