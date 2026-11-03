import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartTotal
/-! Fuel stability for the checked smart-operation infrastructure. These
lemmas compare Flapjack retry implementations and have no HOL counterparts. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

/-- A successful lift remains unchanged with one more unit of fuel. Flapjack retry infrastructure; no HOL counterpart. -/
theorem liftFuel_step (fuel : Nat) : ∀ xs n binds result,
    liftFuel fuel xs n binds = some result → liftFuel (fuel + 1) xs n binds = some result := by
  induction fuel with
  | zero =>
    intro xs n binds result h
    cases xs <;> simp_all [liftFuel]
  | succ fuel ih =>
    intro xs n binds result h
    cases xs with
    | nil => simpa [liftFuel] using h
    | cons x xs =>
      simp only [liftFuel] at h ⊢
      split at *
      · cases hr : liftFuel fuel xs n binds with
        | none => simp [hr] at h
        | some out =>
          have ht := ih xs n binds out hr
          simp [hr, ht] at h ⊢
          simp_all
      · split at *
        · rename_i tag ys hc
          cases hr : liftFuel fuel ys n binds with
          | none => simp [hr] at h
          | some out =>
            rcases out with ⟨ys2, n2, b2⟩
            have ht := ih ys n binds (ys2, n2, b2) hr
            simp only [hr, Option.bind_eq_bind] at h
            cases hx : liftFuel fuel xs n2 b2 with
            | none => simp [hx] at h
            | some out2 =>
              have ht2 := ih xs n2 b2 out2 hx
              simp [ht, ht2, hx] at h ⊢
              simp_all
        · cases hr : liftFuel fuel xs (n + 1) (binds ++ [x]) with
          | none => simp [hr] at h
          | some out =>
            have ht := ih xs (n+1) (binds ++ [x]) out hr
            simp [hr, ht] at h ⊢
            simp_all
/-- Preserve an option bind when a recursive result persists at greater fuel.
Flapjack proof infrastructure; no HOL counterpart. -/
private theorem eqBindStep (fuel : Nat)
    (ih : ∀ pairs result, eqListFuel fuel pairs = some result →
      eqListFuel (fuel + 1) pairs = some result)
    (pairs : List (Exp × Exp)) (k : List Exp → Option (List Exp)) (result : List Exp)
    (h : (eqListFuel fuel pairs).bind k = some result) :
    (eqListFuel (fuel + 1) pairs).bind k = some result := by
  cases hp : eqListFuel fuel pairs with
  | none => simp [hp] at h
  | some value =>
    have hq := ih pairs value hp
    simpa [hp, hq] using h

/-- A successful equality decomposition remains unchanged with one more unit of fuel. Flapjack retry infrastructure; no HOL counterpart. -/
theorem eqListFuel_step (fuel : Nat) : ∀ pairs result,
    eqListFuel fuel pairs = some result → eqListFuel (fuel + 1) pairs = some result := by
  induction fuel with
  | zero =>
    intro pairs result h
    cases pairs <;> simp_all [eqListFuel]
  | succ fuel ih =>
    intro pairs result h
    cases pairs with
    | nil => simpa [eqListFuel] using h
    | cons p rest =>
      rcases p with ⟨x, y⟩
      rw [eqListFuel] at h
      rw [eqListFuel]
      cases hr : eqListFuel fuel rest with
      | none =>
        cases hd : directEq x y <;> cases hx : cons x <;> cases hy : cons y <;> simp_all
      | some rs =>
        have hrs := ih rest rs hr
        simp only [hr, hrs, Option.bind_eq_bind] at h ⊢
        cases hd : directEq x y with
        | some e => simp [hd] at h ⊢; exact h
        | none =>
          simp only [hd] at h ⊢
          cases hx : cons x <;> cases hy : cons y <;> simp [hx, hy] at h ⊢
          all_goals try { exact h }
          all_goals try { exact eqBindStep fuel ih _ _ _ h }
          all_goals split at h <;> split <;> simp_all
          all_goals exact eqBindStep fuel ih _ _ _ h

/-- Increasing lift fuel preserves a successful result. Flapjack retry infrastructure; no HOL counterpart. -/
theorem liftFuel_mono {a b : Nat} (h : a ≤ b) (xs : List Exp) (n : Nat) (binds : List Exp)
    (result : List Exp × Nat × List Exp) :
    liftFuel a xs n binds = some result → liftFuel b xs n binds = some result := by
  induction h with
  | refl => exact id
  | @step b h ih => intro success; exact liftFuel_step b xs n binds result (ih success)

/-- Increasing equality-decomposition fuel preserves a successful result. Flapjack retry infrastructure; no HOL counterpart. -/
theorem eqListFuel_mono {a b : Nat} (h : a ≤ b) (pairs : List (Exp × Exp)) (result : List Exp) :
    eqListFuel a pairs = some result → eqListFuel b pairs = some result := by
  induction h with
  | refl => exact id
  | @step b h ih => intro success; exact eqListFuel_step b pairs result (ih success)

/-- Any two successful lift traversals give the same result. Flapjack retry infrastructure; no HOL counterpart. -/
theorem liftFuel_agree (a b : Nat) (xs : List Exp) (n : Nat) (binds : List Exp)
    (x y : List Exp × Nat × List Exp) (hx : liftFuel a xs n binds = some x)
    (hy : liftFuel b xs n binds = some y) : x = y := by
  have hx2 := liftFuel_mono (Nat.le_max_left a b) xs n binds x hx
  have hy2 := liftFuel_mono (Nat.le_max_right a b) xs n binds y hy
  exact Option.some.inj (hx2.symm.trans hy2)

/-- Any two successful equality decompositions give the same result. Flapjack retry infrastructure; no HOL counterpart. -/
theorem eqListFuel_agree (a b : Nat) (pairs : List (Exp × Exp)) (x y : List Exp)
    (hx : eqListFuel a pairs = some x) (hy : eqListFuel b pairs = some y) : x = y := by
  have hx2 := eqListFuel_mono (Nat.le_max_left a b) pairs x hx
  have hy2 := eqListFuel_mono (Nat.le_max_right a b) pairs y hy
  exact Option.some.inj (hx2.symm.trans hy2)

/-- The total checked lift wrapper is independent of the initial fuel. Flapjack retry infrastructure; no HOL counterpart. -/
theorem liftBounded_independent (a b : Nat) (xs : List Exp) (n : Nat) (binds : List Exp) :
    liftBounded a xs n binds = liftBounded b xs n binds := rfl

/-- The total checked equality wrapper is independent of the initial fuel. Flapjack retry infrastructure; no HOL counterpart. -/
theorem eqListBounded_independent (a b : Nat) (pairs : List (Exp × Exp)) :
    eqListBounded a pairs = eqListBounded b pairs := rfl

/-- The complete checked smart constructor is independent of initial fuel. Flapjack retry infrastructure; no HOL counterpart. -/
theorem smartFuel_independent (a b : Nat) (trace : BackendCommon.Tra) (op : Op) (xs : List Exp) :
    smartFuel a trace op xs = smartFuel b trace op xs := rfl

end Flapjack.Compiler.Backend.ClosOp
