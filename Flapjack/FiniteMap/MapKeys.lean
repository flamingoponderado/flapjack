import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# HOL `finite_map` `MAP_KEYS` on the finite-support carrier

HOL introduces `MAP_KEYS` by `new_specification("MAP_KEYS_def", ["MAP_KEYS"], MAP_KEYS_exists)`
(`HOL/src/finite_maps/finite_mapScript.sml:2620`): the domain of `MAP_KEYS f fm` is the image of
`FDOM fm`, and when `f` is injective on `FDOM fm` it carries every value to the renamed key.
This Flapjack infrastructure renders that constant on `HolFiniteMapExact` by the matching Hilbert
choice over the specification, so outside the injective case nothing beyond the domain is
constrained, as in HOL; `FDOM`/`'` are read through `lookup`. Like the carrier's other library
operations (`updateEq`, `map2`, ...), it is untagged.
-/

namespace Flapjack.HolFiniteMapExact

/-- `HolFiniteMapExact` equality from equal lookups (Flapjack infrastructure). -/
theorem ext_lookup {α β : Type} {m1 m2 : HolFiniteMapExact α β}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [mk.injEq]
  funext k; exact h k

/-- The HOL `MAP_KEYS_def` specification over the finite-support carrier. -/
def MapKeysSpec {α β γ : Type}
    (g : (α → γ) → HolFiniteMapExact α β → HolFiniteMapExact γ β) : Prop :=
  ∀ (f : α → γ) (m : HolFiniteMapExact α β),
    (∀ k, (g f m).lookup k ≠ none ↔ ∃ x, m.lookup x ≠ none ∧ k = f x) ∧
    ((∀ x y, m.lookup x ≠ none → m.lookup y ≠ none → f x = f y → x = y) →
      ∀ x, m.lookup x ≠ none → (g f m).lookup (f x) = m.lookup x)

/-- A witness of the specification, choosing a preimage key. -/
noncomputable def mapKeysWitness {α β γ : Type} (f : α → γ) (m : HolFiniteMapExact α β) :
    HolFiniteMapExact γ β := by
  classical
  exact
    { lookup := fun k => if h : ∃ x, m.lookup x ≠ none ∧ k = f x then m.lookup (Classical.choose h)
        else none
      finiteSupport := by
        obtain ⟨keys, hkeys⟩ := m.finiteSupport
        refine ⟨keys.map f, fun k hk => ?_⟩
        by_cases h : ∃ x, m.lookup x ≠ none ∧ k = f x
        · obtain ⟨x, hx, rfl⟩ := h
          exact List.mem_map.mpr ⟨x, hkeys x hx, rfl⟩
        · simp only [h, dif_neg, not_false_eq_true] at hk
          exact absurd rfl hk }

theorem mapKeysExists {α β γ : Type} :
    ∃ g : (α → γ) → HolFiniteMapExact α β → HolFiniteMapExact γ β, MapKeysSpec g := by
  classical
  refine ⟨mapKeysWitness, fun f m => ⟨fun k => ?_, fun hinj x hx => ?_⟩⟩
  · simp only [mapKeysWitness]
    by_cases h : ∃ x, m.lookup x ≠ none ∧ k = f x
    · simp only [h, dif_pos, ne_eq, iff_true]
      exact (Classical.choose_spec h).1
    · simp only [h, dif_neg, not_false_eq_true, ne_eq, not_true_eq_false]
  · simp only [mapKeysWitness]
    have h : ∃ y, m.lookup y ≠ none ∧ f x = f y := ⟨x, hx, rfl⟩
    rw [dif_pos h]
    obtain ⟨hy, hfy⟩ := Classical.choose_spec h
    rw [hinj _ _ hy hx hfy.symm]

/-- HOL `MAP_KEYS`, rendered by the Hilbert choice over its specification. -/
noncomputable def mapKeys {α β γ : Type} (f : α → γ) (m : HolFiniteMapExact α β) :
    HolFiniteMapExact γ β :=
  Classical.choose (mapKeysExists (α := α) (β := β) (γ := γ)) f m

theorem mapKeys_spec {α β γ : Type} : MapKeysSpec (mapKeys (α := α) (β := β) (γ := γ)) :=
  Classical.choose_spec mapKeysExists

/-- Under an injective `f`, `MAP_KEYS f m` looks up `f x` as `m` looks up `x`. -/
theorem lookup_mapKeys_of_injective {α β γ : Type} {f : α → γ} (hf : Function.Injective f)
    (m : HolFiniteMapExact α β) (x : α) : (mapKeys f m).lookup (f x) = m.lookup x := by
  obtain ⟨hdom, hval⟩ := mapKeys_spec f m
  by_cases hx : m.lookup x = none
  · rw [hx]
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨y, hy, hxy⟩ := (hdom (f x)).mp hne
    rw [hf hxy] at hx; exact hy hx
  · exact hval (fun a b _ _ hab => hf hab) x hx

/-- Keys outside the range of `f` are absent from `MAP_KEYS f m`. -/
theorem lookup_mapKeys_of_not_range {α β γ : Type} {f : α → γ} (m : HolFiniteMapExact α β)
    {k : γ} (hk : ∀ x, k ≠ f x) : (mapKeys f m).lookup k = none := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x, _, rfl⟩ := ((mapKeys_spec f m).1 k).mp hne
  exact hk x rfl

/-- `MAP_KEYS_FUPDATE` for an injective `f` (Flapjack infrastructure; HOL's lemma needs
injectivity only on the updated domain). -/
theorem mapKeys_updateEq {α β γ : Type} [DecidableEq α] [DecidableEq γ] {f : α → γ}
    (hf : Function.Injective f) (m : HolFiniteMapExact α β) (k : α) (v : β) :
    mapKeys f (m.updateEq (k, v)) = (mapKeys f m).updateEq (f k, v) := by
  apply ext_lookup
  intro j
  by_cases hj : ∃ x, j = f x
  · obtain ⟨x, rfl⟩ := hj
    rw [lookup_mapKeys_of_injective hf]
    simp only [updateEq, FUPDATE_HOL]
    by_cases hxk : x = k
    · subst hxk; simp
    · rw [if_neg hxk, if_neg (fun h => hxk (hf h)), lookup_mapKeys_of_injective hf]
  · have hj' : ∀ x, j ≠ f x := fun x h => hj ⟨x, h⟩
    rw [lookup_mapKeys_of_not_range _ hj']
    simp only [updateEq, FUPDATE_HOL]
    rw [if_neg (hj' k), lookup_mapKeys_of_not_range _ hj']

end Flapjack.HolFiniteMapExact
