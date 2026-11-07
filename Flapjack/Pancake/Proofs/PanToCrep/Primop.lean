module

public import Flapjack.HolRef
public import Flapjack.Pancake.Semantics.CrepSem.Primop
public import Flapjack.Pancake.Semantics.PanSem.Primop
public import Flapjack.Pancake.Semantics.PanSem.ValueHOL

@[expose] public section

/-!
The AddCarry primitive case needed by HOL `pc_compile_correct`.
-/

namespace Flapjack


-- Exact-carrier, mapped variant (Flapjack-specific support; NOT the HOL-shaped
-- statement): the HOL statement
-- `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`
-- with `panPrimopHOLExact`/`flattenHOL` over the exact `ValueHOL width`/
-- `HolWordLab width` carriers, but with `crepPrimopHOL` (the untagged executable
-- `PanWordLab (BitVec width)` rendering of `crep_primop_def`).  The exact
-- `HolWordLab` payloads are carried across with `HolWordLab.toPanWordLab`.
-- The HOL-shaped port is `panPrimopCrepPrimopExactHOL` below (tagged
-- `pan_primop_crep_primop`); this mapped variant is kept as untagged support.
theorem panPrimopCrepPrimopHOLExact {width : Nat} [NeZero width]
    (operator : PrimOp) (values : List (ValueHOL width)) (value : ValueHOL width)
    (hprimitive : panPrimopHOLExact operator values = some value) :
    crepPrimopHOL operator
        ((values.flatMap flattenHOL).map HolWordLab.toPanWordLab) =
      some ((flattenHOL value).map HolWordLab.toPanWordLab) := by
  cases operator
  cases values with
  | nil => simp [panPrimopHOLExact] at hprimitive
  | cons first rest =>
      cases rest with
      | nil => simp [panPrimopHOLExact] at hprimitive
      | cons second rest =>
          cases rest with
          | nil => simp [panPrimopHOLExact] at hprimitive
          | cons third rest =>
              cases rest with
              | cons _ _ => simp [panPrimopHOLExact] at hprimitive
              | nil =>
                  cases first <;> cases second <;> cases third <;>
                    simp [panPrimopHOLExact] at hprimitive
                  rename_i left right carry
                  rw [← hprimitive]
                  simp [crepPrimopHOL, flattenHOL, HolWordLab.toPanWordLab]

/-- Exact port of HOL `pan_primop_crep_primop`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096-1099`):
    `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`.
    Both sides use the exact `word_lab` carrier `HolWordLab` and the exact
    `panPrimopHOLExact`/`flattenHOL`/`crepPrimopHOLExact`; there is NO explicit
    `HolWordLab.toPanWordLab` map in the statement, so the shape matches HOL.
    The mapped `PanWordLab` variant is `panPrimopCrepPrimopHOLExact` above
    (untagged support). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pan_primop_crep_primop"]
theorem panPrimopCrepPrimopExactHOL {width : Nat} [NeZero width]
    (operator : PrimOp) (values : List (ValueHOL width)) (value : ValueHOL width)
    (hprimitive : panPrimopHOLExact operator values = some value) :
    crepPrimopHOLExact operator (values.flatMap flattenHOL) =
      some (flattenHOL value) := by
  cases operator
  cases values with
  | nil => simp [panPrimopHOLExact] at hprimitive
  | cons first rest =>
      cases rest with
      | nil => simp [panPrimopHOLExact] at hprimitive
      | cons second rest =>
          cases rest with
          | nil => simp [panPrimopHOLExact] at hprimitive
          | cons third rest =>
              cases rest with
              | cons _ _ => simp [panPrimopHOLExact] at hprimitive
              | nil =>
                  cases first <;> cases second <;> cases third <;>
                    simp [panPrimopHOLExact] at hprimitive
                  rename_i left right carry
                  rw [← hprimitive]
                  simp [crepPrimopHOLExact, flattenHOL]

end Flapjack
