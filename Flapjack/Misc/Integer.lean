import Flapjack.HolRef

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

end Flapjack
