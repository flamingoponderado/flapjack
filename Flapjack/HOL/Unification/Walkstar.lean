module

public import Flapjack.HOL.Unification.Walk.ToVar

@[expose] public section

/-! Unbounded first-order substitution normalization. -/
namespace Flapjack.HOL.Unification

/-- Structural substitution with a proof that all visited variables are covered. -/
def termMap {α : Type} (r : Nat → Prop) (repl : ∀ n, r n → Term α) :
    (t : Term α) → (∀ n, vars t n → r n) → Term α
  | .var n, covered => repl n (covered n rfl)
  | .pair a b, covered =>
      .pair (termMap r repl a (fun n hn => covered n (Or.inl hn)))
        (termMap r repl b (fun n hn => covered n (Or.inr hn)))
  | .const c, _ => .const c

/-- The well-founded recursion body for normalizing one bound variable. -/
def body {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (v : Nat) (repl : ∀ n, vR s n v → Term α) : Term α :=
  match h : s.lookup v with
  | none => .var v
  | some t => termMap (fun n => vR s n v) repl t (by
      intro n hn
      simpa [vR, h] using hn)

/-- Normalize a term using the well-founded dependency relation. -/
noncomputable def normalizeWF {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (h : wfs s) (t : Term α) : Term α :=
  termMap (fun _ => True) (fun v _ => h.fix (body s) v) t (fun _ _ => True.intro)

/-- Pointwise agreement of replacements implies agreement on a term. -/
theorem termMap_congr {α : Type} (r q : Nat → Prop)
    (f : ∀ n, r n → Term α) (g : ∀ n, q n → Term α)
    (t : Term α) (hr : ∀ n, vars t n → r n) (hq : ∀ n, vars t n → q n)
    (eq : ∀ n (hn : vars t n), f n (hr n hn) = g n (hq n hn)) :
    termMap r f t hr = termMap q g t hq := by
  induction t with
  | var n => exact eq n rfl
  | const c => rfl
  | pair a b iha ihb =>
    simp only [termMap]
    congr 1
    · apply iha
      intro n hn
      exact eq n (Or.inl hn)
    · apply ihb
      intro n hn
      exact eq n (Or.inr hn)

/-- Unfold well-founded normalization at a variable. -/
theorem normalizeVar {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (hw : wfs s) (v : Nat) :
    normalizeWF s hw (.var v) = match s.lookup v with
      | none => .var v
      | some t => normalizeWF s hw t := by
  simp only [normalizeWF, termMap]
  rw [WellFounded.fix_eq hw (body s) v]
  unfold body
  split <;> simp_all only
  apply termMap_congr
  intro _ _
  rfl

/-- Normalization is unchanged by walking a variable first. -/
theorem normalizeWalkVar {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (hw : wfs s) : ∀ v, normalizeWF s hw (.var v) = normalizeWF s hw (vwalk s v) := by
  intro v
  induction v using hw.induction with
  | h v ih =>
    have weq := vwalkEq s hw v
    cases found : s.lookup v with
    | none => simp only [found] at weq; rw [weq]
    | some t =>
      cases t with
      | var n =>
        simp only [found] at weq
        rw [normalizeVar s hw v, found, weq]
        apply ih n
        simp [vR, found, vars]
      | pair a b =>
        simp only [found] at weq
        rw [normalizeVar s hw v, found, weq]
      | const c =>
        simp only [found] at weq
        rw [normalizeVar s hw v, found, weq]

/-- First-order walking; inherits the explicit off-wfs choice of `vwalk`. -/
noncomputable def walk {α : Type} (s : HolFiniteMapExact Nat (Term α)) : Term α → Term α
  | .var v => vwalk s v
  | .pair a b => .pair a b
  | .const c => .const c

/-- The well-founded normalizer obeys the recursive walkstar equation. -/
theorem normalizeEq {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (hw : wfs s) (t : Term α) :
    normalizeWF s hw t = match walk s t with
      | .pair a b => .pair (normalizeWF s hw a) (normalizeWF s hw b)
      | x => x := by
  cases t with
  | pair a b => rfl
  | const c => rfl
  | var v =>
    have norm := normalizeWalkVar s hw v
    cases found : vwalk s v with
    | var u =>
      have absent : u ∉ s.domain := vwalkToVar s hw v u found
      have missing : s.lookup u = none := by
        change ¬ (s.lookup u ≠ none) at absent
        exact Classical.not_not.mp absent
      simp only [walk, found, normalizeVar s hw u, missing] at norm ⊢
      exact norm
    | pair a b => simpa [walk, found, normalizeWF, termMap] using norm
    | const c => simpa [walk, found, normalizeWF, termMap] using norm

/-- A total model of HOL's walker normalization. The conditional HOL equation
    constrains well-formed substitutions; the identity choice outside that
    condition is not claimed to match behavior unconstrained by the equation. -/
noncomputable def walkstar {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (t : Term α) : Term α := by
  classical
  exact if h : wfs subst then normalizeWF subst h t else t

/-- The canonical substitution map survives the broad-map codec roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_walkstarEq_subst {α : Type}
    (subst : HolFiniteMapExact Nat (Term α)) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).lookup key = subst.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst)).finiteSupport = subst.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad subst) = subst :=
  holFmapAsFiniteSupportParamWitness_vR_subst subst key

@[hol "HOL/examples/algorithms/unification/triangular/first-order/walkstarScript.sml" "walkstar_def"
  (fmap_as_finite_support_parameters := [subst])]
theorem walkstarEq {α : Type} (subst : HolFiniteMapExact Nat (Term α))
    (h : wfs subst) : ∀ t, walkstar subst t = match walk subst t with
      | .pair a b => .pair (walkstar subst a) (walkstar subst b)
      | x => x := by
  intro t
  classical
  simp only [walkstar, dif_pos h]
  exact normalizeEq subst h t

end Flapjack.HOL.Unification

