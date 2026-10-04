import Flapjack.Compiler.Backend.WordAlloc.Instructions
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

/-!
# Exact live-scoped local lookup transport for Word allocation

Counterpart of `word_allocProofScript.sml:177-253`. Live sets are HOL sets
rendered as predicates on Nat; source and target locals use the exact Spt
carrier. The relation permits arbitrary colour functions, including aliasing
outside the live set. These lemmas do not claim the full allocation simulation.
-/

namespace Flapjack.WordAlloc

/-- HOL's payload-polymorphic live-scoped lookup relation, without any
injectivity assumption or restriction to word-valued locals. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_def"]
def strongLocalsRel {α : Type} (f : Nat → Nat) (live : Nat → Prop)
    (source target : Spt α) : Prop :=
  ∀ n v, live n ∧ sptLookup n source = some v → sptLookup (f n) target = some v

/-- HOL strong_locals_rel_subset_domain with predicate-rendered set inclusion. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_subset_domain"]
theorem strongLocalsRelSubsetDomain {α : Type}
    (f : Nat → Nat) (live : Nat → Prop) (l1 l2 : Spt α)
    (h : strongLocalsRel f live l1 l2 ∧ (∀ n, live n → sptMem n l1)) :
    ∀ v, live v → sptMem (f v) l2 := by
  intro v hv
  obtain ⟨value, hvalue⟩ := (sptMem_iff_lookup v l1).mp (h.2 v hv)
  exact (sptMem_iff_lookup (f v) l2).mpr ⟨value, h.1 v value ⟨hv, hvalue⟩⟩

/-- Exact HOL subset restriction of the generic live-scoped local relation. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_subset"]
theorem strongLocalsRelSubset {α : Type} (f : Nat → Nat) (s larger : Nat → Prop)
    (source target : Spt α)
    (h : (∀ key, s key → larger key) ∧ strongLocalsRel f larger source target) :
    strongLocalsRel f s source target := by
  intro key value hk
  exact h.2 key value ⟨h.1 key hk.1, hk.2⟩

/-- Exact HOL extension when the original live set covers the entire source
map domain. The new live set is arbitrary; no subset restriction is needed. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_extend_aux"]
theorem strongLocalsRelExtendAux {α : Type} (f : Nat → Nat) (s t : Nat → Prop)
    (source target : Spt α)
    (h : (∀ key, sptDomain source key → s key) ∧ strongLocalsRel f s source target) :
    strongLocalsRel f t source target := by
  intro key value hk
  have hmem : sptMem key source := (sptMem_iff_lookup key source).mpr ⟨value, hk.2⟩
  exact h.2 key value ⟨h.1 key hmem, hk.2⟩

namespace StrongLocalsWitnesses

/-- Canonical imported WordSem carrier roundtrip for the local lookup ports. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StrongLocalsWitnesses

/-- HOL strong_locals_rel_get_var over the evaluator's actual state carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelGetVar {width : Nat} [NeZero width] {C F : Type}
    (f : Nat → Nat) (live : Nat → Prop) (st cst : WordSemStateFiniteExact width C F)
    (n : Nat) (x : WordLocW width)
    (h : strongLocalsRel f live st.locals cst.locals ∧ live n ∧
      WordSemStateFiniteExact.getVar n st = some x) :
    WordSemStateFiniteExact.getVar (f n) cst = some x :=
  h.1 n x ⟨h.2.1, h.2.2⟩

/-- Exact HOL register/immediate lookup transport. The live-set membership
condition applies only to registers; immediate success needs no local lookup. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelGetVarImm {width : Nat} [NeZero width] {C F : Type}
    (f : Nat → Nat) (live : Nat → Prop) (st cst : WordSemStateFiniteExact width C F)
    (n : WordRegImm (BitVec width)) (x : WordLocW width)
    (h : strongLocalsRel f live st.locals cst.locals ∧
      (match n with | .reg key => live key | .imm _ => True) ∧
      WordSemStateFiniteExact.getVarImm n st = some x) :
    WordSemStateFiniteExact.getVarImm (applyColourImm f n) cst = some x := by
  cases n with
  | reg key => exact strongLocalsRelGetVar f live st cst key x h
  | imm word => simpa only [applyColourImm, WordSemStateFiniteExact.getVarImm] using h.2.2

/-- HOL strong_locals_rel_get_vars: every requested live source lookup is
transported, preserving list order and duplicates. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem strongLocalsRelGetVars {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ls : List Nat) (y : List (WordLocW width)) (f : Nat → Nat) (live : Nat → Prop)
      (st cst : WordSemStateFiniteExact width C F),
      strongLocalsRel f live st.locals cst.locals ∧ (∀ x, x ∈ ls → live x) ∧
        WordSemStateFiniteExact.getVars ls st = some y →
      WordSemStateFiniteExact.getVars (ls.map f) cst = some y := by
  intro ls
  induction ls with
  | nil =>
      intro y f live st cst h
      simpa [WordSemStateFiniteExact.getVars] using h.2.2
  | cons n ns ih =>
      intro y f live st cst ⟨hrel, hlive, hvars⟩
      cases hv : WordSemStateFiniteExact.getVar n st with
      | none => simp [WordSemStateFiniteExact.getVars, hv] at hvars
      | some v =>
        cases hvs : WordSemStateFiniteExact.getVars ns st with
        | none => simp [WordSemStateFiniteExact.getVars, hv, hvs] at hvars
        | some vs =>
          have hhead := strongLocalsRelGetVar f live st cst n v
            ⟨hrel, hlive n (by simp), hv⟩
          have htail := ih vs f live st cst
            ⟨hrel, fun x hx => hlive x (by simp [hx]), hvs⟩
          simp [WordSemStateFiniteExact.getVars, hv, hvs] at hvars
          subst y
          simp [WordSemStateFiniteExact.getVars, hhead, htail]

/-- HOL strong_locals_rel_UNION; set union is pointwise disjunction. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_UNION"]
theorem strongLocalsRelUnion {α : Type}
    (f : Nat → Nat) (A B : Nat → Prop) (t l : Spt α) :
    strongLocalsRel f (fun n => A n ∨ B n) t l ↔
      strongLocalsRel f A t l ∧ strongLocalsRel f B t l := by
  constructor
  · intro h
    exact ⟨fun n v hn => h n v ⟨Or.inl hn.1, hn.2⟩,
      fun n v hn => h n v ⟨Or.inr hn.1, hn.2⟩⟩
  · rintro ⟨ha, hb⟩ n v ⟨hab, hv⟩
    cases hab with
    | inl ha' => exact ha n v ⟨ha', hv⟩
    | inr hb' => exact hb n v ⟨hb', hv⟩

/-- Exact HOL strong_locals_rel_insert: colours need be injective only on
`n INSERT live`; the old relation is required only on `live DELETE n`.
HOL INJ's codomain UNIV membership is tautological. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "strong_locals_rel_insert"]
theorem strongLocalsRelInsert {α : Type}
    (f : Nat → Nat) (n : Nat) (live : Nat → Prop)
    (source target : Spt α) (value : α)
    (h : (∀ a b, (a = n ∨ live a) → (b = n ∨ live b) → f a = f b → a = b) ∧
      strongLocalsRel f (fun k => live k ∧ k ≠ n) source target) :
    strongLocalsRel f live (sptInsert n value source) (sptInsert (f n) value target) := by
  intro k v ⟨hk, hv⟩
  by_cases heq : k = n
  · subst k
    rw [sptLookup_sptInsert_same] at hv
    cases hv
    exact sptLookup_sptInsert_same (f n) value target
  · rw [sptLookup_sptInsert_ne n k value source heq] at hv
    have hcolour : f k ≠ f n := by
      intro hc
      exact heq (h.1 k n (Or.inr hk) (Or.inl rfl) hc)
    rw [sptLookup_sptInsert_ne (f n) (f k) value target hcolour]
    exact h.2 k v ⟨⟨hk, heq⟩, hv⟩

end Flapjack.WordAlloc
