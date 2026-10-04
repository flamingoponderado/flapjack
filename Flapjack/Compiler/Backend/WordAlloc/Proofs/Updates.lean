import Flapjack.Compiler.Backend.WordAlloc.Proofs.StrongLocalsRel

namespace Flapjack.WordAlloc

/-- Flapjack-specific map-level form of the HOL set_var_dom argument.
It exposes the same scoped injection and successful-source-lookup reasoning
without adding a state carrier or a stronger relation. -/
private theorem insertDom {width : Nat} [NeZero width]
    (f : Nat → Nat) (X d : Nat → Prop) (n : Nat) (v : WordLocW width)
    (src dst : Spt (WordLocW width))
    (hi : ∀ a b, X a → X b → f a = f b → a = b)
    (hs : ∀ k, sptMem k src → X k) (hn : X n)
    (hr : strongLocalsRel f d src dst) :
    strongLocalsRel f d (sptInsert n v src) (sptInsert (f n) v dst) := by
  intro k value ⟨hk, hv⟩
  by_cases he : k = n
  · subst k
    rw [sptLookup_sptInsert_same] at hv
    cases hv
    exact sptLookup_sptInsert_same (f n) v dst
  · rw [sptLookup_sptInsert_ne n k v src he] at hv
    have hx := hs k ((sptMem_iff_lookup k src).mpr ⟨value, hv⟩)
    have hf : f k ≠ f n := fun h => he (hi k n hx hn h)
    rw [sptLookup_sptInsert_ne (f n) (f k) v dst hf]
    exact hr k value ⟨hk, hv⟩

/-- Flapjack-specific domain invariant for the exact HOL alist_insert helper;
HOL proves the analogous membership fact via lookup_alist_insert. -/
private theorem alistInsertDomain {width : Nat} [NeZero width]
    (names : List Nat) (values : List (WordLocW width)) (src : Spt (WordLocW width))
    (X : Nat → Prop) (hs : ∀ k, sptMem k src → X k)
    (hn : ∀ k, k ∈ names → X k) :
    ∀ k, sptMem k (LoopSemStateFiniteExact.sptAlistInsert names values src) → X k := by
  induction names generalizing values with
  | nil => exact hs
  | cons n ns ih =>
    cases values with
    | nil => exact hs
    | cons v vs =>
      intro k hk
      have hd := ih vs (fun k hk => hn k (by simp [hk]))
      rcases (sptMem_sptInsert k n v _).mp hk with he | hm
      · subst k; exact hn n (by simp)
      · exact hd k hm

private theorem alistInsertRel {width : Nat} [NeZero width]
    (names : List Nat) (values : List (WordLocW width)) (f : Nat → Nat)
    (X d : Nat → Prop) (src dst : Spt (WordLocW width))
    (hi : ∀ a b, X a → X b → f a = f b → a = b)
    (hs : ∀ k, sptMem k src → X k) (hn : ∀ k, k ∈ names → X k)
    (hr : strongLocalsRel f d src dst) :
    strongLocalsRel f d (LoopSemStateFiniteExact.sptAlistInsert names values src)
      (LoopSemStateFiniteExact.sptAlistInsert (names.map f) values dst) := by
  induction names generalizing values with
  | nil => exact hr
  | cons n ns ih =>
    cases values with
    | nil => exact hr
    | cons v vs =>
      have hns : ∀ k, k ∈ ns → X k := fun k hk => hn k (by simp [hk])
      exact insertDom f X d n v _ _ hi (alistInsertDomain ns vs src X hs hns)
        (hn n (by simp)) (ih vs hns)

namespace UpdateWitnesses

/-- Same-module re-export of the canonical imported carrier witness. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end UpdateWitnesses

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelSetVarsDom {width : Nat} [NeZero width] {C F : Type}
    (ns : List Nat) (ls : List (WordLocW width)) (f : Nat → Nat) (X d : Nat → Prop)
    (s t : WordSemStateFiniteExact width C F)
    (h : ns.length = ls.length ∧
      (∀ a b, X a → X b → f a = f b → a = b) ∧
      (∀ k, sptMem k s.locals → X k) ∧ (∀ k, k ∈ ns → X k) ∧
      strongLocalsRel f d s.locals t.locals) :
    strongLocalsRel f d (WordSemStateFiniteExact.setVars ns ls s).locals
      (WordSemStateFiniteExact.setVars (ns.map f) ls t).locals :=
  alistInsertRel ns ls f X d s.locals t.locals h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelSetVarDom {width : Nat} [NeZero width] {C F : Type}
    (f : Nat → Nat) (X d : Nat → Prop) (n : Nat) (l : WordLocW width)
    (s t : WordSemStateFiniteExact width C F)
    (h : (∀ a b, X a → X b → f a = f b → a = b) ∧
      (∀ k, sptMem k s.locals → X k) ∧ X n ∧ strongLocalsRel f d s.locals t.locals) :
    strongLocalsRel f d (WordSemStateFiniteExact.setVar n l s).locals
      (WordSemStateFiniteExact.setVar (f n) l t).locals :=
  insertDom f X d n l s.locals t.locals h.1 h.2.1 h.2.2.1 h.2.2.2

end Flapjack.WordAlloc
