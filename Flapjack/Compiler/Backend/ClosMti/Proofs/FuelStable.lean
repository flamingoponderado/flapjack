import Flapjack.Compiler.Backend.ClosMti.Proofs.Total

/-! Successful multi-argument traversals remain stable when given more fuel. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

private def Extends {α : Type} (first second : Option α) : Prop :=
  ∀ value, first = some value → second = some value

private theorem extends_bind {α β : Type} {first second : Option α}
    {f g : α → Option β} (values : Extends first second)
    (continuation : ∀ value, Extends (f value) (g value)) :
    Extends (first.bind f) (second.bind g) := by
  intro result run
  cases first with
  | none => simp at run
  | some value =>
    have same := values value rfl
    simp only [Option.bind_some] at run
    rw [same]
    exact continuation value result run

private theorem extends_mapM {α β : Type} (items : List α) (f g : α → Option β)
    (pointwise : ∀ item ∈ items, Extends (f item) (g item)) :
    Extends (items.mapM f) (items.mapM g) := by
  induction items with
  | nil => intro result run; simpa using run
  | cons item items ih =>
    simp only [List.mapM_cons]
    apply extends_bind (pointwise item (by simp))
    intro result
    apply extends_bind (ih (by intro x hx; exact pointwise x (by simp [hx])))
    intro rest value run
    exact run

macro "prove_stability" r:ident out:ident st:ident sts:ident fs:ident : tactic => `(tactic|
  (rw [introMultiFuel.eq_def] at $r ⊢
   first
   | exact $r
   | apply (show Extends _ _ from ?_) $out $r
     repeat' first | assumption | apply extends_bind | exact $st _ | exact $sts _ | exact $fs _ | intro
  ))

/-- Adding one traversal step preserves every successful output. This is a
property of the executed Lean pass, not yet a port of the total HOL pass. -/
theorem introMultiFuel_succ_of_success (fuel maxApp : Nat) (e result : Exp)
    (run : introMultiFuel fuel maxApp e = some result) :
    introMultiFuel (fuel + 1) maxApp e = some result := by
  induction fuel generalizing e result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have step (body : Exp) : Extends (introMultiFuel fuel maxApp body)
        (introMultiFuel (fuel + 1) maxApp body) := by
      intro value success; exact ih body value success
    have steps (items : List Exp) : Extends
        (items.mapM (introMultiFuel fuel maxApp))
        (items.mapM (introMultiFuel (fuel + 1) maxApp)) := by
      apply extends_mapM
      intro item _; exact step item
    have funSteps (items : List (Nat × Exp)) : Extends
        (items.mapM (fun p => do
          let (arity, body) := collectArgs maxApp p.1 p.2
          pure (arity, ← introMultiFuel fuel maxApp body)))
        (items.mapM (fun p => do
          let (arity, body) := collectArgs maxApp p.1 p.2
          pure (arity, ← introMultiFuel (fuel + 1) maxApp body))) := by
      apply extends_mapM
      intro item _
      obtain ⟨arity, body⟩ := item
      cases found : collectArgs maxApp arity body with
      | mk count inner =>
        dsimp only
        apply extends_bind (step inner)
        intro x value equal
        exact equal
    cases e
    case app t loc body xs => cases loc <;> prove_stability run result step steps funSteps
    case fn t loc vars arity body => cases loc <;> cases vars <;> prove_stability run result step steps funSteps
    case letrec t loc vars funs body => cases loc <;> cases vars <;> prove_stability run result step steps funSteps
    all_goals prove_stability run result step steps funSteps

/-- Successful output is preserved at any larger traversal fuel. -/
theorem introMultiFuel_mono (fuel larger maxApp : Nat) (e result : Exp)
    (le : fuel ≤ larger) (run : introMultiFuel fuel maxApp e = some result) :
    introMultiFuel larger maxApp e = some result := by
  induction le with
  | refl => exact run
  | @step larger _ ih => exact introMultiFuel_succ_of_success larger maxApp e result ih

/-- Two successful traversals cannot disagree, even when their budgets differ. -/
theorem introMultiFuel_unique (fuel₁ fuel₂ maxApp : Nat) (e result₁ result₂ : Exp)
    (first : introMultiFuel fuel₁ maxApp e = some result₁)
    (second : introMultiFuel fuel₂ maxApp e = some result₂) : result₁ = result₂ := by
  have left := introMultiFuel_mono fuel₁ (max fuel₁ fuel₂) maxApp e result₁ (Nat.le_max_left _ _) first
  have right := introMultiFuel_mono fuel₂ (max fuel₁ fuel₂) maxApp e result₂ (Nat.le_max_right _ _) second
  rw [left] at right
  exact Option.some.inj right

/-- A successful retry is the result of a successful ordinary traversal. -/
theorem introMultiBounded_origin (fuel maxApp : Nat) (e result : Exp)
    (run : introMultiBounded fuel maxApp e = some result) :
    ∃ used, introMultiFuel used maxApp e = some result := by
  cases first : introMultiFuel fuel maxApp e with
  | some value =>
    have equal : value = result := by simpa [introMultiBounded, first] using run
    subst value
    exact ⟨fuel, first⟩
  | none =>
    exact ⟨max fuel (expBudget e + 1), by simpa [introMultiBounded, first] using run⟩

/-- The retrying traversal is independent of its initial fuel. -/
theorem introMultiBounded_fuel_independent (fuel₁ fuel₂ maxApp : Nat) (e : Exp) :
    introMultiBounded fuel₁ maxApp e = introMultiBounded fuel₂ maxApp e := by
  obtain ⟨result₁, first⟩ := introMultiBounded_succeeds fuel₁ maxApp e
  obtain ⟨result₂, second⟩ := introMultiBounded_succeeds fuel₂ maxApp e
  obtain ⟨used₁, firstRun⟩ := introMultiBounded_origin fuel₁ maxApp e result₁ first
  obtain ⟨used₂, secondRun⟩ := introMultiBounded_origin fuel₂ maxApp e result₂ second
  have equal := introMultiFuel_unique used₁ used₂ maxApp e result₁ result₂ firstRun secondRun
  rw [first, second, equal]

end Flapjack.Compiler.Backend.ClosMti
