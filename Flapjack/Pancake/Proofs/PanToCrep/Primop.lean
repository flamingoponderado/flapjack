import Flapjack.HolRef
import Flapjack.Pancake.Semantics.CrepSem.Primop
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
The AddCarry primitive case needed by HOL `pc_compile_correct`.
-/

namespace Flapjack

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL
    `pan_primop_crep_primop` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096-1099`):
    `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`.
    A successful source primitive result flattens to exactly the result of the
    Crep primitive on flattened inputs; both sides retain HOL's `word_lab`
    wrapper at this theorem boundary. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed 2026-09-25:
-- statement shape is mirrored clause-for-clause: the single `SOME` implication,
-- the `FLAT (MAP flatten vs)` argument, and the `flatten value` result are all
-- present (`List.flatMap panSemFlattenHOL values`, `panSemFlattenHOL value`).
-- Carrier mismatch: the Lean statement quantifies the production `PanValue`
-- carrier, whose `nStruct` names are `FieldName` = `String` and whose word
-- payload is `BitVec width` with the executable `[NeZero width]` argument,
-- while HOL `panSem$v` uses `fldname` = `mlstring` and `fldname # value` over a
-- positive-width `'a word` without any typeclass side condition. The `flatten`
-- result is a `word_lab list` on both sides (`PanWordLab`).
-- `names_as_string` cannot authorize this: the only identifiers live inside a
-- `PanValue` datatype payload, not at the theorem boundary, and the conclusion
-- is a `SOME`-equation over flattened values, so no `NameRanged` byte witness
-- can be stated. Its dependencies `panPrimopHOL`/`panSemFlattenHOL` had their
-- tags withdrawn for the same reason (`flapjack-0lj.3`).
-- Classified `documented_mismatch` in `docs/HOL-THEOREM-MAP.json`
-- (reviewer flapjack-deepseek-two); the declaration is intentionally untagged.
-- Oracle evidence: `scripts/hol-probes/pan_crep_primop_probe.out` rows
-- `pan_valid=SOME [8;0]`, `pan_overflow=SOME [0;1]`, `pan_invalid=NONE`,
-- `crep_valid=SOME [8;0]`, `crep_overflow=SOME [0;1]`, `crep_invalid=NONE`,
-- `crep_zero_args=NONE`, `crep_four_args=NONE`, `crep_nonzero_carry=SOME [0;1]`,
-- reproduced by `Flapjack/Test/PanCrepPrimopParity.lean` (guards plus the
-- kernel-checked `bridgeFixture` applying this theorem).
-- Exact MlString carrier tracked by `flapjack-pxn.18.3.5.8` / `flapjack-0lj`.
theorem panPrimopCrepPrimop {width : Nat} [NeZero width]
    (operator : PrimOp) (values : List (PanValue (BitVec width)))
    (value : PanValue (BitVec width))
    (hprimitive : panPrimopHOL operator values = some value) :
    crepPrimopHOL operator (values.flatMap panSemFlattenHOL) =
      some (panSemFlattenHOL value) := by
  cases operator
  cases values with
  | nil => simp [panPrimopHOL] at hprimitive
  | cons first rest =>
      cases rest with
      | nil => simp [panPrimopHOL] at hprimitive
      | cons second rest =>
          cases rest with
          | nil => simp [panPrimopHOL] at hprimitive
          | cons third rest =>
              cases rest with
              | cons _ _ => simp [panPrimopHOL] at hprimitive
              | nil =>
                  cases first <;> cases second <;> cases third <;>
                    simp [panPrimopHOL] at hprimitive
                  rw [← hprimitive]
                  simp [crepPrimopHOL, panSemFlattenHOL,
                    panSemFlattenValuesHOL]

-- Exact-carrier counterpart (Flapjack-specific; carry review pending): the HOL
-- statement `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`
-- with `panPrimopHOLExact`/`flattenHOL` over the exact `ValueHOL width`/
-- `HolWordLab width` carriers.  `crepPrimopHOL` is the reviewed `crep_primop_def`
-- port over `PanWordLab (BitVec width)`, so the exact `HolWordLab` payloads are
-- carried across with `HolWordLab.toPanWordLab` (a bijection that is `rfl` on
-- `.word`).  No finite maps occur, so no qualifier applies; not yet tagged
-- `@[hol]` pending coordinator source review of the cross-carrier map.
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

/-- Exact-shape port of HOL `pan_primop_crep_primop`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1096-1099`):
    `pan_primop pop vs = SOME value ==> crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)`.
    Both sides use the exact `word_lab` carrier `HolWordLab` and the exact
    `panPrimopHOLExact`/`flattenHOL`/`crepPrimopHOLExact`; there is NO explicit
    `HolWordLab.toPanWordLab` map in the statement, so the shape matches HOL.
    This is UNTAGGED pending coordinator source review of the newly defined
    exact-carrier `crepPrimopHOLExact` (`flapjack-4ac.5.16.9.1`). -/
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
