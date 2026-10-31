import Flapjack.Compiler.Backend.ClosToBvl.Layout

/-! Accumulator properties of recursive closure code layout. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Appending an existing suffix to the accumulator appends it to the result.
This is Flapjack infrastructure for the source accumulator lemmas. -/
theorem buildAux_append (i : Nat) (entries : List (Nat × Bvl.Exp))
    (before suffix : List (Nat × Nat × Bvl.Exp)) :
    buildAux i entries (before ++ suffix) =
      ((buildAux i entries before).1, (buildAux i entries before).2 ++ suffix) := by
  induction entries generalizing i before with
  | nil => simp [buildAux]
  | cons entry entries ih =>
      rcases entry with ⟨arity, body⟩
      simpa [buildAux, List.cons_append] using ih (i + 2) ((i, arity, body) :: before)

/-- Building recursive entries on an accumulator preserves it as a suffix. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_aux_acc"]
theorem buildAux_acc (entries : List (Nat × Bvl.Exp)) (i : Nat)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    ∃ added, (buildAux i entries aux).2 = added ++ aux := by
  refine ⟨(buildAux i entries []).2, ?_⟩
  simpa using congrArg Prod.snd (buildAux_append i entries [] aux)

/-- The final location and generated prefix are independent of the initial
accumulator. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_aux_MOVE"]
theorem buildAux_move (entries : List (Nat × Bvl.Exp)) (i : Nat)
    (aux : List (Nat × Nat × Bvl.Exp)) (final : Nat)
    (result : List (Nat × Nat × Bvl.Exp)) :
    buildAux i entries aux = (final, result) ↔
      ∃ added, buildAux i entries [] = (final, added) ∧ result = added ++ aux := by
  have relation := buildAux_append i entries [] aux
  cases base : buildAux i entries [] with
  | mk n added =>
      simp only [List.nil_append, base] at relation
      rw [relation]
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨added, ⟨rfl, rfl⟩, rfl⟩
      · rintro ⟨other, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨rfl, rfl⟩

/-- Recursive entries consume two code locations each. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_aux_LENGTH"]
theorem buildAux_length (entries : List (Nat × Bvl.Exp)) (i : Nat)
    (aux : List (Nat × Nat × Bvl.Exp)) (final : Nat)
    (result : List (Nat × Nat × Bvl.Exp))
    (built : buildAux i entries aux = (final, result)) : final = i + 2 * entries.length := by
  induction entries generalizing i aux with
  | nil =>
      simp [buildAux] at built
      simpa using built.1.symm
  | cons entry entries ih =>
      rcases entry with ⟨arity, body⟩
      have next := ih (i + 2) ((i, arity, body) :: aux) (by simpa [buildAux] using built)
      simp only [List.length_cons]
      omega

/-- Every generated recursive entry remains in the resulting auxiliary list at
its corresponding even-spaced location. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "build_aux_MEM"]
theorem buildAux_mem (entries : List (Nat × Bvl.Exp)) (i : Nat)
    (aux : List (Nat × Nat × Bvl.Exp)) (final : Nat)
    (result : List (Nat × Nat × Bvl.Exp))
    (built : buildAux i entries aux = (final, result)) (k : Nat) (bound : k < entries.length) :
    ∃ item : Nat × Bvl.Exp, (i + 2 * k, item) ∈ result := by
  induction entries generalizing i aux k with
  | nil => simp at bound
  | cons entry entries ih =>
      rcases entry with ⟨arity, body⟩
      have next : buildAux (i + 2) entries ((i, arity, body) :: aux) = (final, result) := by
        simpa [buildAux] using built
      cases k with
      | zero =>
          obtain ⟨added, acc⟩ := buildAux_acc entries (i + 2) ((i, arity, body) :: aux)
          rw [next] at acc
          change result = added ++ (i, arity, body) :: aux at acc
          refine ⟨(arity, body), ?_⟩
          rw [acc]
          simp
      | succ k =>
          have bound' : k < entries.length := by simp at bound; omega
          obtain ⟨item, found⟩ := ih (i + 2) ((i, arity, body) :: aux) next k bound'
          have eq : i + 2 + 2 * k = i + 2 * (k + 1) := by omega
          exact ⟨item, by simpa only [eq] using found⟩

end Flapjack.Compiler.Backend.ClosToBvl
