import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Decidable renderings of HOL `sptree$domain` set conditions

wordSem `evaluate_def` (`cakeml/compiler/backend/semantics/wordSemScript.sml`,
the `Call` clause) tests two HOL set conditions on `sptree$domain`: the
empty-cutset guard `domain (FST names) = {}`, and the locals check
`domain s1.locals = domain (FST envs) UNION domain (SND envs)` (bead
`flapjack-h29l.8.1`).  HOL `domain t` is the set of keys present in `t`, and
set equality is extensional.  So these are rendered as membership predicates
over `sptMem`:
* `sptDomainEmpty a` is `∀ k, ¬ sptMem k a`;
* `sptDomainEqUnion a b c` is `∀ k, sptMem k a ↔ sptMem k b ∨ sptMem k c`.

Both are decided by enumerating the finite key sets.  The union
inclusion uses the enumeration `sptSubsetUnionAux`, whose correctness is
kernel-checked (`sptSubsetUnionAux_eq_true`).  HOL `domain` and set
operations come from the HOL standard library, so these are untagged Flapjack
infrastructure.
-/

namespace Flapjack

open LoopSemStateFiniteExact

instance sptMemDecidable {α : Type} (k : Nat) (t : Spt α) : Decidable (sptMem k t) := by
  unfold sptMem sptDomain; infer_instance

/-- HOL `domain a = {}`: no key is present. -/
def sptDomainEmpty {α : Type} (a : Spt α) : Prop := ∀ k, ¬ sptMem k a

/-- HOL `domain a = domain b UNION domain c`, extensionally. -/
def sptDomainEqUnion {α β γ : Type} (a : Spt α) (b : Spt β) (c : Spt γ) : Prop :=
  ∀ k, sptMem k a ↔ sptMem k b ∨ sptMem k c

/-- Enumerate the keys of `left` through an absolute-key map `g`, and check
    each is present in `right1` or `right2`. -/
def sptSubsetUnionAux {α β γ : Type} (right1 : Spt β) (right2 : Spt γ) (g : Nat → Nat) :
    Spt α → Bool
  | .ln => true
  | .ls _ => (sptLookup (g 0) right1).isSome || (sptLookup (g 0) right2).isSome
  | .bn first second =>
      sptSubsetUnionAux right1 right2 (fun m => g (2 * m + 2)) first &&
        sptSubsetUnionAux right1 right2 (fun m => g (2 * m + 1)) second
  | .bs first _ second =>
      ((sptLookup (g 0) right1).isSome || (sptLookup (g 0) right2).isSome) &&
        (sptSubsetUnionAux right1 right2 (fun m => g (2 * m + 2)) first &&
          sptSubsetUnionAux right1 right2 (fun m => g (2 * m + 1)) second)

private theorem sptMem_or_isSome {β γ : Type} (r1 : Spt β) (r2 : Spt γ) (k : Nat) :
    ((sptLookup k r1).isSome || (sptLookup k r2).isSome) = true ↔ sptMem k r1 ∨ sptMem k r2 := by
  rw [Bool.or_eq_true, sptMem_iff_lookup, sptMem_iff_lookup, Option.isSome_iff_exists,
    Option.isSome_iff_exists]

/-- The union enumeration accepts exactly when every key of `left`, mapped by
    `g`, lies in `right1` or `right2`. -/
theorem sptSubsetUnionAux_eq_true {α β γ : Type} (right1 : Spt β) (right2 : Spt γ) :
    ∀ (g : Nat → Nat) (left : Spt α),
      sptSubsetUnionAux right1 right2 g left = true ↔
        ∀ key, sptMem key left → sptMem (g key) right1 ∨ sptMem (g key) right2 := by
  intro g left
  induction left generalizing g with
  | ln => simp [sptSubsetUnionAux]
  | ls value =>
      simp only [sptSubsetUnionAux, sptMem_or_isSome]
      constructor
      · intro h key hk
        have hk0 : key = 0 := (sptMem_ls key value).mp hk
        subst hk0; exact h
      · intro h; exact h 0 ((sptMem_ls 0 value).mpr rfl)
  | bn first second ihl ihr =>
      simp only [sptSubsetUnionAux, Bool.and_eq_true, sptMem_bn]
      rw [ihl (fun m => g (2 * m + 2)), ihr (fun m => g (2 * m + 1))]
      constructor
      · rintro ⟨hl, hr⟩ key (⟨m, hm, hk⟩ | ⟨m, hm, hk⟩)
        · subst hk; exact hl m hm
        · subst hk; exact hr m hm
      · intro h
        exact ⟨fun m hm => h (2 * m + 2) (Or.inl ⟨m, hm, rfl⟩),
          fun m hm => h (2 * m + 1) (Or.inr ⟨m, hm, rfl⟩)⟩
  | bs first value second ihl ihr =>
      simp only [sptSubsetUnionAux, Bool.and_eq_true, sptMem_bs, sptMem_or_isSome]
      rw [ihl (fun m => g (2 * m + 2)), ihr (fun m => g (2 * m + 1))]
      constructor
      · rintro ⟨h0, hl, hr⟩ key (h0' | ⟨m, hm, hk⟩ | ⟨m, hm, hk⟩)
        · subst h0'; exact h0
        · subst hk; exact hl m hm
        · subst hk; exact hr m hm
      · intro h
        exact ⟨h 0 (Or.inl rfl),
          fun m hm => h (2 * m + 2) (Or.inr (Or.inl ⟨m, hm, rfl⟩)),
          fun m hm => h (2 * m + 1) (Or.inr (Or.inr ⟨m, hm, rfl⟩))⟩

theorem sptDomainEmpty_iff {α : Type} (a : Spt α) :
    sptDomainEmpty a ↔ sptSubsetLive a (.ln : Spt Unit) := by
  unfold sptDomainEmpty sptSubsetLive
  constructor
  · intro h k hk; exact absurd hk (h k)
  · intro h k hk
    have := h k hk
    simp [sptMem, sptDomain, sptLookup] at this

instance sptDomainEmptyDecidable {α : Type} (a : Spt α) : Decidable (sptDomainEmpty a) :=
  decidable_of_iff _ (sptDomainEmpty_iff a).symm

theorem sptDomainEqUnion_iff {α β γ : Type} (a : Spt α) (b : Spt β) (c : Spt γ) :
    sptDomainEqUnion a b c ↔
      sptSubsetUnionAux b c id a = true ∧ sptSubsetLive b a ∧ sptSubsetLive c a := by
  rw [sptSubsetUnionAux_eq_true]
  unfold sptDomainEqUnion sptSubsetLive
  constructor
  · intro h
    exact ⟨fun k hk => (h k).1 hk, fun k hk => (h k).2 (Or.inl hk), fun k hk => (h k).2 (Or.inr hk)⟩
  · rintro ⟨h1, h2, h3⟩ k
    exact ⟨h1 k, fun h => h.elim (h2 k) (h3 k)⟩

instance sptDomainEqUnionDecidable {α β γ : Type} (a : Spt α) (b : Spt β) (c : Spt γ) :
    Decidable (sptDomainEqUnion a b c) :=
  decidable_of_iff _ (sptDomainEqUnion_iff a b c).symm

end Flapjack
