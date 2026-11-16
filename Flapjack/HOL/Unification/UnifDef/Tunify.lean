module

public import Flapjack.HOL.Unification.UnifDef.WellFounded
public import Flapjack.HOL.Unification.Walkstar.Occurs

@[expose] public section

namespace Flapjack.HOL.Unification

/-- Recursion body for the restricted proof model; not a separate HOL port. -/
noncomputable def tunifyAuxBody {α : Type}
    (p : HolFiniteMapExact Nat (Term α) × Term α × Term α)
    (rec : ∀ q, uR q p → Option (HolFiniteMapExact Nat (Term α))) :
    Option (HolFiniteMapExact Nat (Term α)) := by
  classical
  let call (q : HolFiniteMapExact Nat (Term α) × Term α × Term α) :=
    if h : uR q p then rec q h else none
  let (subst, left, right) := p
  exact if wfs subst then
    match walk subst left, walk subst right with
    | .var v1, .var v2 => some (if v1 = v2 then subst else subst.updateEq (v1, .var v2))
    | .var v, other => if Oc subst other v then none else some (subst.updateEq (v, other))
    | other, .var v => if Oc subst other v then none else some (subst.updateEq (v, other))
    | .pair a d, .pair b e => (call (subst, a, b)).bind (fun sx => call (sx, d, e))
    | .const a, .const b => if a = b then some subst else none
    | _, _ => none
  else none

/-- A proof-side approximation of HOL's restricted well-founded recursion.
    It chooses `none` outside well-formed states and for recursive calls not
    justified by `uR`; HOL leaves those values arbitrary. The required
    equality with HOL's total unifier remains to be established, so this
    model is not tagged as the original definition. -/
noncomputable def tunifyAux {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) : Option (HolFiniteMapExact Nat (Term α)) :=
  uRWellFounded.fix tunifyAuxBody (s, t1, t2)

/-- Unfold the restricted recursion once, for the invariant proof. -/
theorem tunifyAuxEq {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α) :
    tunifyAux s t1 t2 = tunifyAuxBody (s, t1, t2)
      (fun q _ => tunifyAux q.1 q.2.1 q.2.2) := by
  unfold tunifyAux
  rw [WellFounded.fix_eq]

private theorem identityUP {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) (hw : wfs s) : uP s s t1 t2 := by
  exact ⟨hw, (fun _ _ found => found), fun _ found => Or.inr found⟩

private theorem updateUP {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) (v : Nat) (hw : wfs s)
    (left : walk s t1 = .var v) (no : ¬ Oc s (walk s t2) v) :
    uP (s.updateEq (v, walk s t2)) s t1 t2 := by
  have free := (walkToVar s t1 v ⟨hw, left⟩).1
  have noVars : ¬ vars (walkstar s t2) v := by
    intro hv
    apply no
    apply (ocEqVarsWalkstar s (walk s t2) v hw).2
    rwa [walkstarWalk s t2 hw]
  exact uPFupdate s v t1 t2 ⟨hw, free, noVars, left⟩

/-- The proof model preserves the substitution invariant required by HOL's
    restricted recursion. Correspondence with `tunify_tupled_aux` remains
    to be established, so this is not yet tagged as `aux_uP`. -/
theorem tunifyAuxUP {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α)
    (sx : HolFiniteMapExact Nat (Term α))
    (h : wfs s ∧ tunifyAux s t1 t2 = some sx) : uP sx s t1 t2 := by
  classical
  have gen : ∀ p : HolFiniteMapExact Nat (Term α) × Term α × Term α,
      wfs p.1 → ∀ sx, tunifyAux p.1 p.2.1 p.2.2 = some sx →
        uP sx p.1 p.2.1 p.2.2 := by
    intro p
    induction p using uRWellFounded.induction with
    | h p ih =>
      rcases p with ⟨s, t1, t2⟩
      intro hw sx result
      rw [tunifyAuxEq] at result
      cases l : walk s t1 <;> cases r : walk s t2 <;>
        simp only [tunifyAuxBody, hw, ↓reduceIte, l, r] at result
      case var.var =>
        rename_i x y
        split at result
        · simp only [Option.some.injEq] at result
          subst sx
          exact identityUP s t1 t2 hw
        · rename_i neq
          simp only [Option.some.injEq] at result
          subst sx
          have free := (walkToVar s t2 y ⟨hw, r⟩).1
          have wy : walk s (.var y) = .var y := by
            simp [walk, notFdomVwalk s y ⟨hw, free⟩]
          have no : ¬ Oc s (walk s t2) x := by
            rw [r, ocEqVarsWalkstar s (.var y) x hw, walkstarEq s hw, wy]
            exact neq
          exact r ▸ updateUP s t1 t2 x hw l no
      case var.pair | var.const =>
        split at result
        · contradiction
        · rename_i no
          simp only [Option.some.injEq] at result
          subst sx
          exact r ▸ updateUP s t1 t2 _ hw l (r ▸ no)
      case pair.var | const.var =>
        split at result
        · contradiction
        · rename_i no
          simp only [Option.some.injEq] at result
          subst sx
          apply (uPSym _ s t2 t1).mp
          exact l ▸ updateUP s t2 t1 _ hw r (l ▸ no)
      case pair.pair =>
        rename_i a d b e
        have headRel := (uRSubterm s t1 t2 a d b e ⟨hw, l, r⟩).1
        simp only [headRel, ↓reduceDIte] at result
        cases first : tunifyAux s a b with
        | none => simp [first] at result
        | some mid =>
          have headUP : uP mid s a b := ih (s, a, b) headRel hw mid first
          have tailRel := uPImpSubtermUR mid s t1 t2 a d b e ⟨hw, l, r, Or.inl headUP⟩
          simp [first, Option.bind, tailRel] at result
          have tailUP : uP sx mid d e := ih (mid, d, e) tailRel headUP.1 sx result
          exact ⟨tailUP.1, (fun k v found => tailUP.2.1 _ _ (headUP.2.1 _ _ found)),
            fun k found => tailRel.2.2.1 (tailUP.2.2 found)⟩
      case pair.const | const.pair => contradiction
      case const.const =>
        split at result
        · simp only [Option.some.injEq] at result
          subst sx
          exact identityUP s t1 t2 hw
        · contradiction
  exact gen (s, t1, t2) h.1 sx h.2


/-- On well-formed substitutions, the restricted calls have the recursive
    equation used by the source unifier. The model's choice outside that
    domain still requires a separate correspondence review. -/
theorem tunifyAuxEquation {α : Type} (s : HolFiniteMapExact Nat (Term α))
    (t1 t2 : Term α) (hw : wfs s) :
    tunifyAux s t1 t2 = by
      classical
      exact match walk s t1, walk s t2 with
        | .var v1, .var v2 => some (if v1 = v2 then s else s.updateEq (v1, .var v2))
        | .var v, other => if Oc s other v then none else some (s.updateEq (v, other))
        | other, .var v => if Oc s other v then none else some (s.updateEq (v, other))
        | .pair a d, .pair b e => (tunifyAux s a b).bind (fun sx => tunifyAux sx d e)
        | .const a, .const b => if a = b then some s else none
        | _, _ => none := by
  classical
  rw [tunifyAuxEq]
  cases l : walk s t1 <;> cases r : walk s t2 <;>
    simp only [tunifyAuxBody, hw, ↓reduceIte, l, r]
  case pair.pair a d b e =>
    have headRel := (uRSubterm s t1 t2 a d b e ⟨hw, l, r⟩).1
    simp only [headRel, ↓reduceDIte]
    cases first : tunifyAux s a b with
    | none => rfl
    | some mid =>
      have headUP := tunifyAuxUP s a b mid ⟨hw, first⟩
      have tailRel := uPImpSubtermUR mid s t1 t2 a d b e ⟨hw, l, r, Or.inl headUP⟩
      simp [Option.bind, tailRel]

/-- Induction following both recursive calls of the proof-side unifier.
    This establishes the induction structure used by `unify_ind`; its
    correspondence to HOL's specified unifier is still pending. -/
theorem tunifyAuxInd {α : Type}
    (P : HolFiniteMapExact Nat (Term α) → Term α → Term α → Prop)
    (step : ∀ s t1 t2,
      (∀ a d b e sx, wfs s ∧ walk s t1 = .pair a d ∧ walk s t2 = .pair b e ∧
        tunifyAux s a b = some sx → P sx d e) ∧
      (∀ a d b e, wfs s ∧ walk s t1 = .pair a d ∧ walk s t2 = .pair b e →
        P s a b) → P s t1 t2) :
    ∀ s t1 t2, P s t1 t2 := by
  have induction : ∀ p : HolFiniteMapExact Nat (Term α) × Term α × Term α,
      P p.1 p.2.1 p.2.2 := by
    intro p
    induction p using uRWellFounded.induction with
    | h p ih =>
      rcases p with ⟨s, t1, t2⟩
      apply step
      constructor
      · intro a d b e sx h
        have up := tunifyAuxUP s a b sx ⟨h.1, h.2.2.2⟩
        exact ih (sx, d, e) (uPImpSubtermUR sx s t1 t2 a d b e
          ⟨h.1, h.2.1, h.2.2.1, Or.inl up⟩)
      · intro a d b e h
        exact ih (s, a, b) (uRSubterm s t1 t2 a d b e h).1
  intro s t1 t2
  exact induction (s, t1, t2)

end Flapjack.HOL.Unification
