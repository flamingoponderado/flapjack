import Flapjack.Compiler.Backend.WordBignum.Equality

/-! Reflection for structural equality of bignum generator syntax. -/
namespace Flapjack.Compiler.Backend.WordBignum

theorem expEq_iff [DecidableEq α] (x y : WordLangExpHOL α) : expEq x y = true ↔ x = y := by
  refine WordLangExpHOL.rec
    (motive_1 := fun x => ∀ y, expEq x y = true ↔ x = y)
    (motive_2 := fun xs => ∀ ys, expListEq xs ys = true ↔ xs = ys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x y
  · intro value other; cases other <;> simp [expEq]
  · intro name other; cases other <;> simp [expEq]
  · intro store other; cases other <;> simp [expEq]
  · intro address ih other; cases other <;> simp [expEq, ih]
  · intro op args ih other; cases other <;> simp [expEq, ih]
  · intro op left right ihl ihr other; cases other <;> simp [expEq, ihl, ihr, and_assoc]
  · intro other; cases other <;> simp [expListEq]
  · intro head tail ihh iht other; cases other <;> simp [expListEq, ihh, iht]

theorem miniEq_iff [DecidableEq α] (x y : Mini α) : miniEq x y = true ↔ x = y := by
  induction x generalizing y <;> cases y <;> simp_all [miniEq, expEq_iff, and_assoc]

/-- Structural equality supplies a decidable, exact equality for mini-programs. -/
instance [DecidableEq α] : DecidableEq (Mini α) := fun x y =>
  decidable_of_iff (miniEq x y = true) (miniEq_iff x y)

end Flapjack.Compiler.Backend.WordBignum
