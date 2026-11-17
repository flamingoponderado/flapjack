module

public import Flapjack.HOL.Unification.Subst
public import Flapjack.FiniteMap.DomainExact
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

/-! Well-formed finite substitutions have exactly the acyclic dependencies. -/
namespace Flapjack.HOL.Unification

/-- The substitution survives the canonical finite-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_wfsNoCycles_s {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s :=
  holFmapAsFiniteSupportParamWitness_vR_subst s key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/substScript.sml" "wfs_no_cycles"
  (fmap_as_finite_support_parameters := [s])]
theorem wfsNoCycles {α : Type} (s : HolFiniteMapExact Nat (Term α)) :
    wfs s ↔ ∀ v, ¬ Relation.TransGen (vR s) v v := by
  constructor
  · intro hw v
    exact hw.transGen.irrefl.irrefl v
  · intro h
    obtain ⟨keys, hkeys⟩ := s.finiteSupport
    have hd : s.domain.Finite := by
      apply (keys.toFinset.finite_toSet).subset
      intro x hx
      exact List.mem_toFinset.mpr (hkeys x hx)
    let : Finite s.domain := hd.to_subtype
    let r : s.domain → s.domain → Prop := fun a b => Relation.TransGen (vR s) a b
    let : IsTrans s.domain r := ⟨by intro a b c hab hbc; exact hab.trans hbc⟩
    let : Std.Irrefl r := ⟨by intro a; exact h a.1⟩
    have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
    have absentAcc : ∀ x, x ∉ s.domain → Acc (vR s) x := by
      intro x hx
      apply Acc.intro
      intro y hy
      apply False.elim
      apply hx
      change s.lookup x ≠ none
      cases found : s.lookup x with
      | none => simp [vR, found] at hy
      | some t => simp
    have inAcc : ∀ a : s.domain, Acc (vR s) a.1 := by
      intro a
      induction a using wf.induction with
      | h a ih =>
        apply Acc.intro
        intro y hy
        by_cases hyD : y ∈ s.domain
        · exact ih ⟨y, hyD⟩ (.single hy)
        · exact absentAcc y hyD
    change WellFounded (vR s)
    constructor
    intro x
    by_cases hx : x ∈ s.domain
    · exact inAcc ⟨x, hx⟩
    · exact absentAcc x hx

end Flapjack.HOL.Unification
