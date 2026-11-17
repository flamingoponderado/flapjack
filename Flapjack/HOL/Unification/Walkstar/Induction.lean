module

public import Flapjack.HOL.Unification.Walkstar
public import Flapjack.HOL.Unification.Walk.Dependency

@[expose] public section

/-! The first-order normalization induction principle. -/
namespace Flapjack.HOL.Unification

/-- The original induction step, named for the structural proof. -/
private def walkstarIndStep {α : Type} (s : HolFiniteMapExact Nat (Term α)) (P : Term α → Prop) : Prop :=
  ∀ t, ((∀ a b, walk s t = .pair a b → P b) ∧
        (∀ a b, walk s t = .pair a b → P a)) → P t

/-- Build the property of a term from the properties of its variables. -/
private theorem buildP {α : Type} (s : HolFiniteMapExact Nat (Term α)) (P : Term α → Prop)
    (step : walkstarIndStep s P) (t : Term α) (known : ∀ v, vars t v → P (.var v)) : P t := by
  cases t with
  | var v => exact known v rfl
  | const c =>
    apply step (.const c)
    constructor <;> intro a b h <;> simp [walk] at h
  | pair a b =>
    apply step (.pair a b)
    constructor
    · intro x y h
      simp only [walk, Term.pair.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact buildP s P step b (fun v hv => known v (Or.inr hv))
    · intro x y h
      simp only [walk, Term.pair.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact buildP s P step a (fun v hv => known v (Or.inl hv))

/-- The canonical substitution survives the broad-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarInd_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_ind"
  (fmap_as_finite_support_parameters := [s])]
theorem walkstarInd {α : Type} (s : HolFiniteMapExact Nat (Term α)) (hw : wfs s) :
    ∀ P : Term α → Prop,
      (∀ t, ((∀ a b, walk s t = .pair a b → P b) ∧
             (∀ a b, walk s t = .pair a b → P a)) → P t) → ∀ t, P t := by
  intro P step
  have allVars : ∀ v, P (.var v) := by
    intro v
    induction v using hw.transGen.induction with
    | h v ih =>
      apply step (.var v)
      constructor
      · intro a b hpair
        apply buildP s P step b
        intro u hu
        apply ih u
        apply vwalkVR s hw v u
        constructor
        · have hv : vars (.pair a b) u := Or.inr hu
          have hvwalk : vwalk s v = .pair a b := by simpa [walk] using hpair
          rw [hvwalk]
          exact hv
        · have : vwalk s v = .pair a b := by simpa [walk] using hpair
          rw [this]
          simp
      · intro a b hpair
        apply buildP s P step a
        intro u hu
        apply ih u
        apply vwalkVR s hw v u
        constructor
        · have hv : vars (.pair a b) u := Or.inl hu
          have hvwalk : vwalk s v = .pair a b := by simpa [walk] using hpair
          rw [hvwalk]
          exact hv
        · have : vwalk s v = .pair a b := by simpa [walk] using hpair
          rw [this]
          simp
  intro t
  exact buildP s P step t (fun v _ => allVars v)

end Flapjack.HOL.Unification
