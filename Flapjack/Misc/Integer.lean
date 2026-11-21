module

public import Flapjack.HolRef

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Integer division and remainder with HOL's partial specification.
The HOL constants are introduced by `new_specification`, whose equations only
constrain nonzero divisors. The choices below preserve that distinction. -/
namespace Flapjack

private def holIntDivBody (i j : Int) : Int :=
  if 0 < j then
    if 0 ≤ i then Int.ofNat (i.toNat / j.toNat)
    else -(Int.ofNat ((-i).toNat / j.toNat)) +
      if (-i).toNat % j.toNat = 0 then 0 else -1
  else
    if 0 ≤ i then -(Int.ofNat (i.toNat / (-j).toNat)) +
      if i.toNat % (-j).toNat = 0 then 0 else -1
    else Int.ofNat ((-i).toNat / (-j).toNat)

private theorem holIntDivExists : ∃ f : Int → Int → Int,
    ∀ i j, j ≠ 0 → f i j = holIntDivBody i j :=
  ⟨holIntDivBody, by intros; rfl⟩

/-- HOL's specified integer division; its value at divisor zero is unconstrained. -/
@[hol "HOL/src/integer/integerScript.sml" "int_div"]
noncomputable def holIntDiv : Int → Int → Int := Classical.choose holIntDivExists

/-- The chosen division obeys its nonzero-divisor specification. This is
Flapjack proof infrastructure. -/
theorem holIntDiv_spec (i j : Int) (h : j ≠ 0) : holIntDiv i j = holIntDivBody i j :=
  Classical.choose_spec holIntDivExists i j h

private theorem holIntModExists : ∃ f : Int → Int → Int,
    ∀ i j, j ≠ 0 → f i j = i - holIntDiv i j * j :=
  ⟨fun i j => i - holIntDiv i j * j, by intros; rfl⟩

/-- HOL's specified remainder; its value at divisor zero is unconstrained. -/
@[hol "HOL/src/integer/integerScript.sml" "int_mod"]
noncomputable def holIntMod : Int → Int → Int := Classical.choose holIntModExists

/-- The chosen remainder obeys its nonzero-divisor specification. This is
Flapjack proof infrastructure. -/
theorem holIntMod_spec (i j : Int) (h : j ≠ 0) : holIntMod i j = i - holIntDiv i j * j :=
  Classical.choose_spec holIntModExists i j h

/-- HOL division of naturals by a positive divisor (Flapjack proof infrastructure). -/
theorem holIntDiv_ofNat_ofNat (a b : Nat) (hb : 0 < b) :
    holIntDiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := by
  rw [holIntDiv_spec _ _ (by omega)]
  simp only [holIntDivBody]
  rw [if_pos (by omega), if_pos (by omega)]
  simp

/-- HOL division of a nonpositive dividend by a positive divisor rounds down
(Flapjack proof infrastructure). -/
theorem holIntDiv_neg_ofNat (a b : Nat) (hb : 0 < b) :
    holIntDiv (-(a : Int)) (b : Int) =
      -((a / b : Nat) : Int) + if a % b = 0 then 0 else -1 := by
  rw [holIntDiv_spec _ _ (by omega)]
  simp only [holIntDivBody]
  rw [if_pos (by omega)]
  by_cases a0 : a = 0
  · subst a0; simp
  · rw [if_neg (by omega)]
    simp [Int.toNat_natCast]

/-- HOL division of a nonnegative dividend by a negative divisor rounds down
(Flapjack proof infrastructure). -/
theorem holIntDiv_ofNat_neg (a b : Nat) (hb : 0 < b) :
    holIntDiv (a : Int) (-(b : Int)) =
      -((a / b : Nat) : Int) + if a % b = 0 then 0 else -1 := by
  rw [holIntDiv_spec _ _ (by omega)]
  simp only [holIntDivBody]
  rw [if_neg (by omega), if_pos (by omega)]
  simp [Int.toNat_natCast]

/-- HOL division of a nonpositive dividend by a negative divisor
(Flapjack proof infrastructure). -/
theorem holIntDiv_neg_neg (a b : Nat) (hb : 0 < b) :
    holIntDiv (-(a : Int)) (-(b : Int)) = ((a / b : Nat) : Int) := by
  rw [holIntDiv_spec _ _ (by omega)]
  simp only [holIntDivBody]
  rw [if_neg (by omega)]
  by_cases a0 : a = 0
  · subst a0; simp
  · rw [if_neg (by omega)]
    simp [Int.toNat_natCast]

end Flapjack
