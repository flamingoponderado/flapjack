import Flapjack.Compiler.Backend.ClosOp
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang
/-- Decompose a successful traversal into its first pair and tail. This is Flapjack proof infrastructure. -/
private theorem decompose (fuel : Nat) (p : Exp × Exp) (rest : List (Exp × Exp)) :
    eqListFuel (fuel + 1) (p :: rest) = (do
      let first ← eqListFuel (fuel + 1) [p]
      let tail ← eqListFuel fuel rest
      pure (first ++ tail)) := by
  obtain ⟨x,y⟩ := p
  simp only [eqListFuel]
  cases hd : directEq x y <;> cases hx : cons x <;> cases hy : cons y <;> simp_all
  all_goals try (split <;> simp_all)
  all_goals simp [Option.bind_assoc]

/-- A singleton fuel traversal agrees with the source tree. This is Flapjack proof infrastructure. -/
private theorem single (fuel : Nat)
    (ih : ∀ pairs result, eqListFuel fuel pairs = some result → appListAppend (eqPureList pairs) = result)
    (x y : Exp) (result : List Exp)
    (h : eqListFuel (fuel + 1) [(x,y)] = some result) :
    appListAppend (eqPureList [(x,y)]) = result := by
  simp only [eqListFuel] at h
  rw [eqPureList]
  cases hd : directEq x y with
  | some z => simp_all [appListAppend, appendAux]
  | none =>
    cases hx : cons x with
    | none =>
      cases hy : cons y with
      | none => simp_all [appListAppend, appendAux]
      | some p =>
        simp only [hd, hx, hy] at h ⊢
        cases hr : eqListFuel fuel [(y,x)] with
        | none => simp [hr] at h
        | some r => simp [hr] at h; subst result; exact ih _ _ hr
    | some p =>
      obtain ⟨tag,xs⟩ := p
      cases hy : cons y with
      | none =>
        simp only [hd, hx, hy] at h ⊢
        cases hr : eqListFuel fuel ((xs.reverse.zip (List.range xs.length)).map fun (e,i) =>
            (e, Exp.op .none (.blockOp (.elemAt i)) [y])) with
        | none => simp [hr] at h
        | some r =>
          simp [hr] at h
          subst result
          rw [(appListAppend_thm _ _ ([] : List Exp)).1, ih _ _ hr]
          rfl
      | some p =>
        obtain ⟨tag2,ys⟩ := p
        simp only [hd, hx, hy] at h ⊢
        by_cases he : (tag != tag2 || xs.length != ys.length) = true
        · simp [he, appListAppend, appendAux] at h ⊢
          exact h
        · simp only [he] at h ⊢
          cases hr : eqListFuel fuel (xs.reverse.zip ys.reverse) with
          | none => simp [hr] at h
          | some r => simp [hr] at h; subst result; exact ih _ _ hr

/-- Every successful fuel traversal equals the flattening of the source tree. This is Flapjack preservation infrastructure, with no separate HOL declaration. -/
theorem eqFuelFlatten (fuel : Nat) : ∀ pairs result,
    eqListFuel fuel pairs = some result → appListAppend (eqPureList pairs) = result := by
  induction fuel with
  | zero =>
    intro pairs result h
    cases pairs <;> simp_all [eqListFuel, eqPureList, appListAppend, appendAux]
  | succ fuel ih =>
    intro pairs result h
    cases pairs with
    | nil => simp_all [eqListFuel, eqPureList, appListAppend, appendAux]
    | cons p rest =>
      cases rest with
      | nil =>
        obtain ⟨x,y⟩ := p
        exact single fuel ih x y result h
      | cons q rest =>
        rw [decompose] at h
        cases hf : eqListFuel (fuel+1) [p] with
        | none => simp [hf] at h
        | some first =>
          cases ht : eqListFuel fuel (q::rest) with
          | none => simp [hf,ht] at h
          | some tail =>
            simp [hf,ht] at h
            subst result
            rw [eqPureList, (appListAppend_thm _ _ ([] : List Exp)).1]
            obtain ⟨x,y⟩ := p
            rw [single fuel ih x y first hf, ih _ _ ht]
end Flapjack.Compiler.Backend.ClosOp
