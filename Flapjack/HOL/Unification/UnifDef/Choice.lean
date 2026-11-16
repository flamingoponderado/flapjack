module

public import Flapjack.HOL.Unification.UnifDef.Tunify

@[expose] public section

/-! Choice and uniqueness for the guarded first-order unifier specification. -/
namespace Flapjack.HOL.Unification

/-- The guarded equation used by HOL's choice specification. This predicate
    is Lean infrastructure for constructing the chosen function; it is not a
    separate HOL declaration. -/
def UnifySpec {α : Type}
    (u : HolFiniteMapExact Nat (Term α) → Term α → Term α → Option (HolFiniteMapExact Nat (Term α))) : Prop :=
  ∀ s t1 t2, wfs s → u s t1 t2 = by
    classical
    exact match walk s t1, walk s t2 with
      | .var v1, .var v2 => some (if v1 = v2 then s else s.updateEq (v1, .var v2))
      | .var v, other => if Oc s other v then none else some (s.updateEq (v, other))
      | other, .var v => if Oc s other v then none else some (s.updateEq (v, other))
      | .pair a d, .pair b e => (u s a b).bind (fun sx => u sx d e)
      | .const a, .const b => if a = b then some s else none
      | _, _ => none

/-- The restricted recursion witnesses the guarded source specification.
    This is Lean choice infrastructure, with no separate HOL declaration. -/
theorem unifySpecExists {α : Type} : ∃ u, @UnifySpec α u :=
  ⟨tunifyAux, fun s t1 t2 hw => tunifyAuxEquation s t1 t2 hw⟩

/-- Select a function satisfying the source unifier specification. This is
    untagged until the option-wrapped finite-map result has a reviewed HOL
    representation qualifier. Outside `wfs` the specification is silent. -/
noncomputable def specifiedUnify {α : Type}
    (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α) : Option (HolFiniteMapExact Nat (Term α)) :=
  Classical.choose (@unifySpecExists α) s t1 t2

private theorem specifiedUnifySpec {α : Type} : @UnifySpec α specifiedUnify :=
  Classical.choose_spec (@unifySpecExists α)

private theorem unifySpecEqAux {α : Type}
    (u : HolFiniteMapExact Nat (Term α) → Term α → Term α → Option (HolFiniteMapExact Nat (Term α)))
    (spec : UnifySpec u) (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α)
    (hw : wfs s) : u s t1 t2 = tunifyAux s t1 t2 := by
  have all : ∀ s (t1 t2 : Term α), wfs s → u s t1 t2 = tunifyAux s t1 t2 := by
    apply tunifyAuxInd
    intro s t1 t2 ih hw
    rw [spec s t1 t2 hw, tunifyAuxEquation s t1 t2 hw]
    cases l : walk s t1 <;> cases r : walk s t2 <;> simp only
    case pair.pair a d b e =>
      rw [ih.2 a d b e ⟨hw, l, r⟩ hw]
      cases first : tunifyAux s a b with
      | none => rfl
      | some mid =>
        have midWfs := (tunifyAuxUP s a b mid ⟨hw, first⟩).1
        simp only [Option.bind]
        exact ih.1 a d b e mid ⟨hw, l, r, first⟩ midWfs
  exact all s t1 t2 hw

/-- The chosen specification and restricted recursion agree under the source
    guard. This is infrastructure for HOL's `unify_eq_tunify`: the right
    side is the Lean auxiliary model, not yet a reviewed HOL `tunify` port. -/
theorem specifiedUnifyEqAux {α : Type} (s : HolFiniteMapExact Nat (Term α)) (t1 t2 : Term α)
    (hw : wfs s) : specifiedUnify s t1 t2 = tunifyAux s t1 t2 :=
  unifySpecEqAux specifiedUnify specifiedUnifySpec s t1 t2 hw

end Flapjack.HOL.Unification
