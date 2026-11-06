import Flapjack.Compiler.Backend.Semantics.DataSem.Space

/-! Architecture and representation limits for data-language operations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Basis.Pure.MlString
open Classical

/-- Bounds for the constant parts consumed by `Build`. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "lim_safe_part_def"]
noncomputable def limSafePart (limits : Limits) : ClosLang.ConstPart → Prop
  | .con tag xs =>
      if xs = [] then tag < 2 ^ archSize limits / 16 else
        xs.length < 2 ^ limits.lengthLimit ∧ xs.length < 2 ^ (archSize limits - 4) ∧
        4 * tag < 2 ^ archSize limits / 16 ∧ 4 * tag < 2 ^ (archSize limits - limits.lengthLimit - 2)
  | .int i => if smallNum limits.arch64Bit i then True else bignumSize limits.arch64Bit i ≤ 2 ^ limits.lengthLimit
  | .str text =>
      let length := text.explode.length
      length / (archSize limits / 8) < 2 ^ archSize limits / archSize limits ∧
      length / (archSize limits / 8) + 1 < 2 ^ limits.lengthLimit ∧
      smallNum limits.arch64Bit (Int.ofNat length)
  | .w64 _ => 1 < limits.lengthLimit

/-- Source limits on one operation and its argument values. Malformed
arguments retain the original permissive fallback where specified. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "lim_safe_def"]
noncomputable def limSafe (limits : Limits) : ClosLang.Op → List Value → Prop
  | .blockOp (.cons tag), xs =>
      if xs = [] then tag < 2 ^ archSize limits / 16 else
        xs.length < 2 ^ limits.lengthLimit ∧ xs.length < 2 ^ (archSize limits - 4) ∧
        4 * tag < 2 ^ archSize limits / 16 ∧ 4 * tag < 2 ^ (archSize limits - limits.lengthLimit - 2)
  | .memOp (.mutCons tag _), xs =>
      xs.length < 2 ^ limits.lengthLimit ∧ xs.length < 2 ^ (archSize limits - 4) ∧
      4 * tag < 2 ^ archSize limits / 16 ∧ 4 * tag < 2 ^ (archSize limits - limits.lengthLimit - 2)
  | .blockOp (.fromList tag), [len, value] =>
      match valueToList value with
      | none => True
      | some values =>
          if len = .number (Int.ofNat values.length) then
            smallNum limits.arch64Bit (Int.ofNat values.length) ∧
            values.length < 2 ^ limits.lengthLimit ∧ values.length < archSize limits / 16 ∧
            4 * tag < 2 ^ (archSize limits - limits.lengthLimit - 2) ∧ 4 * tag < 2 ^ archSize limits / 16
          else True
  | .blockOp .listAppend, [a, b] =>
      match valueToList a, valueToList b with
      | some xs, some _ => 1 < limits.lengthLimit ∧ 3 * (xs.length + 1) < 2 ^ archSize limits / 8
      | _, _ => True
  | .blockOp (.consExtend tag), .block _ _ xs' :: .number lower :: .number len :: .number total :: xs =>
      if lower < 0 ∨ len < 0 ∨ lower + len > Int.ofNat xs'.length ∨
         total = 0 ∨ total ≠ Int.ofNat xs.length + len then True else
        let length := (xs ++ (xs'.drop lower.toNat).take len.toNat).length
        length < 2 ^ limits.lengthLimit ∧ length < 2 ^ archSize limits / 16 ∧
        4 * tag < 2 ^ archSize limits / 16 ∧ 4 * tag < 2 ^ (archSize limits - limits.lengthLimit - 2)
  | .intOp .add, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ smallNum limits.arch64Bit b ∧ smallNum limits.arch64Bit (a + b)
      then True else bignumSize limits.arch64Bit a + bignumSize limits.arch64Bit b ≤ 2 ^ limits.lengthLimit
  | .intOp .sub, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ smallNum limits.arch64Bit b ∧ smallNum limits.arch64Bit (a - b)
      then True else bignumSize limits.arch64Bit a + bignumSize limits.arch64Bit b ≤ 2 ^ limits.lengthLimit
  | .intOp .mult, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (a * b) then True
      else bignumSize limits.arch64Bit a + bignumSize limits.arch64Bit b ≤ 2 ^ limits.lengthLimit
  | .intOp .div, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (holIntDiv a b) then True
      else bignumSize limits.arch64Bit a + bignumSize limits.arch64Bit b ≤ 2 ^ limits.lengthLimit
  | .intOp .mod, [.number a, .number b] =>
      if smallNum limits.arch64Bit a ∧ 0 ≤ a ∧ smallNum limits.arch64Bit b ∧ 0 ≤ b ∧
         smallNum limits.arch64Bit (holIntMod a b) then True
      else bignumSize limits.arch64Bit a + bignumSize limits.arch64Bit b ≤ 2 ^ limits.lengthLimit
  | .memOp .refArray, [.number i, _] =>
      0 ≤ i ∧ i.toNat < 2 ^ archSize limits / 16 ∧ i.toNat < 2 ^ limits.lengthLimit
  | .memOp (.refByte _), .number i :: _ =>
      0 ≤ i ∧ i.toNat / (archSize limits / 8) < 2 ^ archSize limits / archSize limits ∧
      i.toNat / (archSize limits / 8) + 1 < 2 ^ limits.lengthLimit ∧ smallNum limits.arch64Bit i
  | .memOp .ref, xs => xs.length < 2 ^ limits.lengthLimit ∧ xs.length < 2 ^ archSize limits / 16
  | .blockOp (.build parts), _ => ∀ part ∈ parts, limSafePart limits part
  | .wordOp .wordToInt, _ | .wordOp .wordFromInt, _ | .wordOp (.wordOpw .w64 _), _
  | .wordOp (.wordShift .w64 _ _), _ | .wordOp (.wordFromWord _), _ => 1 < limits.lengthLimit
  | .wordOp (.fpCmp _), _ => limits.hasFpOps = true
  | .wordOp (.fpUop _), _ | .wordOp (.fpBop _), _ =>
      limits.hasFpOps = true ∧ (limits.arch64Bit = true ∨ 1 < limits.lengthLimit)
  | .wordOp (.fpTop _), _ =>
      limits.hasFpOps = true ∧ limits.hasFpTops = true ∧ (limits.arch64Bit = true ∨ 1 < limits.lengthLimit)
  | _, _ => True

/-- Preserve safety only if the current operation meets its limits. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_lim_safe"]
noncomputable def doLimSafe {C F : Type} (state : State C F) (op : ClosLang.Op) (values : List Value) : State C F :=
  { state with safeForSpace := decide (limSafe state.limits op values) && state.safeForSpace }

/-- Preserve safety only if a length fits the configured limit. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "check_lim_def"]
def checkLim {C F : Type} (state : State C F) (length : Nat) : State C F :=
  { state with safeForSpace := decide (length < 2 ^ state.limits.lengthLimit) && state.safeForSpace }

end Flapjack.Compiler.Backend.DataSem
