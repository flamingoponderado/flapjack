import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileTotal

/-! Successful bounded mini-compilation does not change when given more fuel.
This is a Flapjack infrastructure fact, not a HOL compiler correctness theorem. -/
namespace Flapjack.Compiler.Backend.WordBignum

theorem compileFuel_mono {width : Nat} [NeZero width] (fuel : Nat) :
    ∀ more n l i (cs : CodeAcc width) (code : Mini (BitVec width)) result,
      fuel ≤ more → compileFuel fuel n l i cs code = some result →
      compileFuel more n l i cs code = some result := by
  induction fuel with
  | zero =>
    intro more n l i cs code result le h
    simp [compileFuel] at h
  | succ fuel ih =>
    intro more n l i cs code result le h
    cases more with
    | zero => omega
    | succ more =>
      have hm : fuel ≤ more := by omega
      cases code with
      | seq a b =>
        cases ha : compileFuel fuel n l i cs a with
        | none => simp [compileFuel, ha] at h
        | some first =>
          obtain ⟨a', la, ia, ca⟩ := first
          have ha' := ih more n l i cs a _ hm ha
          cases hb : compileFuel fuel n la ia ca b with
          | none => simp [compileFuel, ha, hb] at h
          | some second =>
            obtain ⟨b', lb, ib, cb⟩ := second
            have hb' := ih more n la ia ca b _ hm hb
            simp [compileFuel, ha, hb] at h
            simpa [compileFuel, ha', hb'] using h
      | ite op r arg a b =>
        cases ha : compileFuel fuel n l i cs a with
        | none => simp [compileFuel, ha] at h
        | some first =>
          obtain ⟨a', la, ia, ca⟩ := first
          have ha' := ih more n l i cs a _ hm ha
          cases hb : compileFuel fuel n la ia ca b with
          | none => simp [compileFuel, ha, hb] at h
          | some second =>
            obtain ⟨b', lb, ib, cb⟩ := second
            have hb' := ih more n la ia ca b _ hm hb
            cases arg <;> simp [compileFuel, ha, hb] at h <;>
              simpa [compileFuel, ha', hb'] using h
      | loop recs live body =>
        cases hc : hasCompiled body cs with
        | inl existing => simpa [compileFuel, hc] using h
        | inr index =>
          cases hb : compileFuel fuel index 2 1 (codeAccNext cs) body with
          | none => simp [compileFuel, hc, hb] at h
          | some compiled =>
            obtain ⟨body', label, temp, entries⟩ := compiled
            have hb' := ih more index 2 1 (codeAccNext cs) body _ hm hb
            simp [compileFuel, hc, hb] at h
            simpa [compileFuel, hc, hb'] using h
      | loopBody body =>
        exact ih more n l i cs body result hm h
      | _ => simpa [compileFuel] using h

/-- Any two successful traversals produce the same result. -/
theorem compileFuel_unique {width : Nat} [NeZero width] (fuel more n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width)) (left right :
      WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width)
    (hl : compileFuel fuel n l i cs code = some left)
    (hr : compileFuel more n l i cs code = some right) : left = right := by
  have hleft := compileFuel_mono fuel (max fuel more) n l i cs code left (Nat.le_max_left _ _) hl
  have hright := compileFuel_mono more (max fuel more) n l i cs code right (Nat.le_max_right _ _) hr
  exact Option.some.inj (hleft.symm.trans hright)

/-- The total entry point returns the result of any successful fuelled run. -/
theorem compile_eq_of_success {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width))
    (result : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width)
    (h : compileFuel fuel n l i cs code = some result) : compile n l i cs code = result := by
  have bound : miniBudget code < miniBudget code + 1 := by omega
  obtain ⟨canonical, hc⟩ := compileFuel_succeeds (miniBudget code + 1) n l i cs code bound
  have same := compileFuel_unique _ _ n l i cs code canonical result hc h
  simp [compile, hc, same]

/-- Every bounded retry agrees with the total entry point. -/
theorem compileBounded_eq_compile {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width)) :
    compileBounded fuel n l i cs code = some (compile n l i cs code) := by
  cases h : compileFuel fuel n l i cs code with
  | some result =>
    have eq := compile_eq_of_success fuel n l i cs code result h
    simp [compileBounded, h, eq]
  | none =>
    have bound : miniBudget code < max fuel (miniBudget code + 1) := by omega
    obtain ⟨result, done⟩ := compileFuel_succeeds _ n l i cs code bound
    have eq := compile_eq_of_success _ n l i cs code result done
    simp [compileBounded, h, done, eq]

end Flapjack.Compiler.Backend.WordBignum
