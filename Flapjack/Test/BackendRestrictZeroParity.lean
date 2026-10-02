import Flapjack.Compiler.Backend.BackendProps
namespace Flapjack.Test.BackendRestrictZeroParity
open Flapjack.Compiler.Backend.BackendProps
example : restrictZero ∅ = ∅ := by ext p; simp [restrictZero]
example : (7,0) ∈ restrictZero {(7,0), (7,1)} := by simp [restrictZero]
example : (7,1) ∉ restrictZero {(7,0), (7,1)} := by simp [restrictZero]
example : (0,7) ∉ restrictZero {(0,7)} := by simp [restrictZero]
example : (8,0) ∉ restrictZero {(7,0)} := by simp [restrictZero]
example : (1208925819614629174706176,0) ∈ restrictZero {(1208925819614629174706176,0)} := by simp [restrictZero]
example : (7,0) ∈ restrictZero Set.univ ∧ (7,1) ∉ restrictZero Set.univ := by simp [restrictZero]
-- Generic kernel consumer preserves arbitrary (including infinite) input sets.
example (labels : Set (Nat × Nat)) (p : Nat × Nat) :
    p ∈ restrictZero labels ↔ p ∈ labels ∧ p.2 = 0 := Iff.rfl
end Flapjack.Test.BackendRestrictZeroParity
