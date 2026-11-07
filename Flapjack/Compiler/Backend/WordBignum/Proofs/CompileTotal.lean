import Flapjack.Compiler.Backend.WordBignum.Compile

/-! Fuel sufficiency for the executable mini-language compiler. This is a
Flapjack infrastructure fact, not a HOL compiler correctness theorem. -/
namespace Flapjack.Compiler.Backend.WordBignum

theorem compileFuel_succeeds {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width)) (bound : miniBudget code < fuel) :
    ∃ result, compileFuel fuel n l i cs code = some result := by
  induction fuel generalizing n l i cs code with
  | zero => omega
  | succ fuel ih =>
    cases code with
    | seq a b =>
      have ba : miniBudget a < fuel := by simp_all [miniBudget] <;> omega
      have bb : miniBudget b < fuel := by simp_all [miniBudget] <;> omega
      obtain ⟨⟨a', la, ia, ca⟩, ha⟩ := ih n l i cs a ba
      obtain ⟨⟨b', lb, ib, cb⟩, hb⟩ := ih n la ia ca b bb
      exact ⟨_, by simp [compileFuel, ha, hb]; rfl⟩
    | ite op r arg a b =>
      have ba : miniBudget a < fuel := by simp_all [miniBudget] <;> omega
      have bb : miniBudget b < fuel := by simp_all [miniBudget] <;> omega
      obtain ⟨⟨a', la, ia, ca⟩, ha⟩ := ih n l i cs a ba
      obtain ⟨⟨b', lb, ib, cb⟩, hb⟩ := ih n la ia ca b bb
      cases arg <;> exact ⟨_, by simp [compileFuel, ha, hb]; rfl⟩
    | loop recs live body =>
      have bb : miniBudget body < fuel := by simp_all [miniBudget] <;> omega
      cases h : hasCompiled body cs with
      | inl index => exact ⟨_, by simp [compileFuel, h]; rfl⟩
      | inr index =>
        obtain ⟨⟨body', lb, ib, cb⟩, hb⟩ := ih index 2 1 (codeAccNext cs) body bb
        exact ⟨_, by simp [compileFuel, h, hb]; rfl⟩
    | loopBody body =>
      have bb : miniBudget body < fuel := by simp_all [miniBudget] <;> omega
      exact ih n l i cs body bb
    | _ => exact ⟨_, rfl⟩

theorem compileBounded_succeeds {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width)) :
    ∃ result, compileBounded fuel n l i cs code = some result := by
  cases h : compileFuel fuel n l i cs code with
  | some result => exact ⟨result, by simp [compileBounded, h]⟩
  | none =>
    have bound : miniBudget code < max fuel (miniBudget code + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds _ n l i cs code bound
    exact ⟨result, by simp [compileBounded, h, done]⟩

theorem compileBounded_eq_of_success {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width))
    (result : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width)
    (h : compileFuel fuel n l i cs code = some result) :
    compileBounded fuel n l i cs code = some result := by
  simp [compileBounded, h]

end Flapjack.Compiler.Backend.WordBignum
