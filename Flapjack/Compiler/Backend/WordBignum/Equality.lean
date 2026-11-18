module

public import Flapjack.Compiler.Backend.WordBignum.Mini

@[expose] public section

/-! Structural equality for bignum generator syntax. These Flapjack helper
definitions and reflection proofs support the source generator's lookup. -/
namespace Flapjack.Compiler.Backend.WordBignum

mutual
def expEq [DecidableEq α] : WordLangExpHOL α → WordLangExpHOL α → Bool
  | .const x, .const y => decide (x = y)
  | .var x, .var y => decide (x = y)
  | .lookup x, .lookup y => decide (x = y)
  | .load x, .load y => expEq x y
  | .op op xs, .op op' ys => decide (op = op') && expListEq xs ys
  | .shift op x y, .shift op' x' y' => decide (op = op') && expEq x x' && expEq y y'
  | _, _ => false
termination_by x _ => sizeOf x
decreasing_by all_goals simp_wf <;> omega

def expListEq [DecidableEq α] : List (WordLangExpHOL α) → List (WordLangExpHOL α) → Bool
  | [], [] => true
  | x :: xs, y :: ys => expEq x y && expListEq xs ys
  | _, _ => false
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

def miniEq [DecidableEq α] : Mini α → Mini α → Bool
  | .skip, .skip | .swap, .swap | .continue, .continue => true
  | .assign a e, .assign b f => decide (a = b) && expEq e f
  | .delete a, .delete b => decide (a = b)
  | .seq a b, .seq c d => miniEq a c && miniEq b d
  | .load a b c, .load d e f => decide (a = d ∧ b = e ∧ c = f)
  | .store a b, .store c d => decide (a = c ∧ b = d)
  | .ite op a b c d, .ite op' a' b' c' d' =>
      decide (op = op' ∧ a = a' ∧ b = b') && miniEq c c' && miniEq d d'
  | .add a b c d e, .add a' b' c' d' e' => decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e')
  | .sub a b c d e, .sub a' b' c' d' e' => decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e')
  | .mul a b c d, .mul a' b' c' d' => decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d')
  | .div a b c d e, .div a' b' c' d' e' => decide (a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e')
  | .loop r vs body, .loop r' vs' body' => decide (r = r' ∧ vs = vs') && miniEq body body'
  | .recurse a b, .recurse c d => decide (a = c ∧ b = d)
  | .loopBody a, .loopBody b => miniEq a b
  | _, _ => false
termination_by x _ => sizeOf x
decreasing_by all_goals simp_wf <;> omega

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
