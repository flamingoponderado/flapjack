import Flapjack.Misc.BinaryIeeeArithFp64
import Flapjack.Misc.Fp64NanRefinement

/-!
# Computable binary64 arithmetic with a canonical quiet NaN

These Flapjack-specific executable producers have no HOL declaration of their
own. Each follows the reviewed roundTiesToEven arithmetic branch structure,
replacing only HOL's unspecified quiet-NaN choice by a concrete quiet NaN.
Unconditional refinement theorems relate the whole result to the original
rendering; they assert bit equality in every non-choice branch. WordSem
instruction/evaluator routing remains a separate acceptance obligation.
Only roundTiesToEven is used by the five arithmetic WordSem Inst clauses.
They observe the word result, not IEEE flags. These proofs compare the existing
rational rendering; they retain its SOUNDNESS item 8 real-rounding assumption
and do not claim a cross-assistant equivalence theorem.
-/
namespace Flapjack

/-- Executable add with original finite/infinite behavior and canonical choice NaN. -/
def execFloatAddRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => defaultQuietNanFloat
  | _, .nan => defaultQuietNanFloat
  | .infinity, .infinity =>
      if x.sign = y.sign then (x)
      else defaultQuietNanFloat
  | .infinity, _ => (x)
  | _, .infinity => (y)
  | .float r1, .float r2 =>
      holFp64RoundTiesToEven
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign = y.sign then x.sign = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)
        (r1 + r2)

/-- Whole-result refinement for arbitrary inputs; no NaN or successful-operation premise. -/
theorem holFloatAddRte64_refines_exec (x y : HolFloat 52 11) :
    holFloatRefines (holFloatAddRte64 x y) (execFloatAddRte64 x y) := by
  unfold holFloatAddRte64 execFloatAddRte64
  try dsimp only
  repeat' split
  all_goals first
    | (exfalso; simp_all; done)
    | (simp_all; exact Or.inl rfl)
    | exact Or.inl rfl
    | exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Executable sub with original finite/infinite behavior and canonical choice NaN. -/
def execFloatSubRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  match holFloatValue x, holFloatValue y with
  | .nan, _ => defaultQuietNanFloat
  | _, .nan => defaultQuietNanFloat
  | .infinity, .infinity =>
      if x.sign = y.sign then defaultQuietNanFloat
      else (x)
  | .infinity, _ => (x)
  | _, .infinity => (holFloatNegate y)
  | .float r1, .float r2 =>
      holFp64RoundTiesToEven
        (if r1 = 0 ∧ r2 = 0 ∧ x.sign ≠ y.sign then x.sign = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)
        (r1 - r2)

/-- Whole-result refinement for arbitrary inputs; no NaN or successful-operation premise. -/
theorem holFloatSubRte64_refines_exec (x y : HolFloat 52 11) :
    holFloatRefines (holFloatSubRte64 x y) (execFloatSubRte64 x y) := by
  unfold holFloatSubRte64 execFloatSubRte64
  try dsimp only
  repeat' split
  all_goals first
    | (exfalso; simp_all; done)
    | (simp_all; exact Or.inl rfl)
    | exact Or.inl rfl
    | exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Executable mul with original finite/infinite behavior and canonical choice NaN. -/
def execFloatMulRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  let signedInf : HolFloat 52 11 :=
    if x.sign = y.sign then holFloatPlusInfinity 52 11 else holFloatMinusInfinity 52 11
  match holFloatValue x, holFloatValue y with
  | .nan, _ => defaultQuietNanFloat
  | _, .nan => defaultQuietNanFloat
  | .infinity, .float r =>
      if r = 0 then defaultQuietNanFloat
      else (signedInf)
  | .float r, .infinity =>
      if r = 0 then defaultQuietNanFloat
      else (signedInf)
  | .infinity, .infinity => (signedInf)
  | .float r1, .float r2 => holFp64RoundTiesToEven (x.sign ≠ y.sign) (r1 * r2)

/-- Whole-result refinement for arbitrary inputs; no NaN or successful-operation premise. -/
theorem holFloatMulRte64_refines_exec (x y : HolFloat 52 11) :
    holFloatRefines (holFloatMulRte64 x y) (execFloatMulRte64 x y) := by
  unfold holFloatMulRte64 execFloatMulRte64
  try dsimp only
  repeat' split
  all_goals first
    | (exfalso; simp_all; done)
    | (simp_all; exact Or.inl rfl)
    | exact Or.inl rfl
    | exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Executable div with original finite/infinite behavior and canonical choice NaN. -/
def execFloatDivRte64 (x y : HolFloat 52 11) : HolFloat 52 11 :=
  let signedInf : HolFloat 52 11 :=
    if x.sign = y.sign then holFloatPlusInfinity 52 11 else holFloatMinusInfinity 52 11
  match holFloatValue x, holFloatValue y with
  | .nan, _ => defaultQuietNanFloat
  | _, .nan => defaultQuietNanFloat
  | .infinity, .infinity => defaultQuietNanFloat
  | .infinity, _ => (signedInf)
  | _, .infinity =>
      (if x.sign = y.sign then holFloatPlusZero 52 11 else holFloatMinusZero 52 11)
  | .float r1, .float r2 =>
      if r2 = 0 then
        if r1 = 0 then defaultQuietNanFloat
        else (signedInf)
      else holFp64RoundTiesToEven (x.sign ≠ y.sign) (r1 / r2)

/-- Whole-result refinement for arbitrary inputs; no NaN or successful-operation premise. -/
theorem holFloatDivRte64_refines_exec (x y : HolFloat 52 11) :
    holFloatRefines (holFloatDivRte64 x y) (execFloatDivRte64 x y) := by
  unfold holFloatDivRte64 execFloatDivRte64
  try dsimp only
  repeat' split
  all_goals first
    | (exfalso; simp_all; done)
    | (simp_all; exact Or.inl rfl)
    | exact Or.inl rfl
    | exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Executable muladd with original finite/infinite behavior and canonical choice NaN. -/
def execFloatMulAddRte64 (x y z : HolFloat 52 11) : HolFloat 52 11 :=
  let signP := x.sign ^^^ y.sign
  let infP := holFloatIsInfinite x || holFloatIsInfinite y
  if holFloatIsNan x || holFloatIsNan y || holFloatIsNan z then
    defaultQuietNanFloat
  else if (holFloatIsInfinite x && holFloatIsZero y) || (holFloatIsZero x && holFloatIsInfinite y) ||
      (holFloatIsInfinite z && infP && decide (signP ≠ z.sign)) then
    defaultQuietNanFloat
  else if (holFloatIsInfinite z && decide (z.sign = 0)) || (infP && decide (signP = 0)) then
    (holFloatPlusInfinity 52 11)
  else if (holFloatIsInfinite z && decide (z.sign = 1)) || (infP && decide (signP = 1)) then
    (holFloatMinusInfinity 52 11)
  else
    let r1 := holFloatToReal x * holFloatToReal y
    let r2 := holFloatToReal z
    let r := r1 + r2
    holFp64RoundTiesToEven
      (decide (r = 0 ∧
          (if r1 = 0 ∧ r2 = 0 ∧ signP = z.sign then signP = 1 else .roundTiesToEven = HolRounding.roundTowardNegative)) ||
        decide (r < 0))
      r

/-- Whole-result refinement for arbitrary inputs; no NaN or successful-operation premise. -/
theorem holFloatMulAddRte64_refines_exec (x y z : HolFloat 52 11) :
    holFloatRefines (holFloatMulAddRte64 x y z) (execFloatMulAddRte64 x y z) := by
  unfold holFloatMulAddRte64 execFloatMulAddRte64
  try dsimp only
  repeat' split
  all_goals first
    | (exfalso; simp_all; done)
    | (simp_all; exact Or.inl rfl)
    | exact Or.inl rfl
    | exact holFloatSomeQnan_refines_defaultQuietNanFloat _

/-- Flapjack codec infrastructure: splitting the concatenated fields returns the
original float exactly. This has no separate CakeML declaration. -/
theorem fp64ToFloat_floatToFp64_exec (x : HolFloat 52 11) : holFp64ToFloat (holFloatToFp64 x) = x := by
  obtain ⟨sign, exponent, significand⟩ := x
  simp only [holFp64ToFloat, holFloatToFp64, HolFloat.mk.injEq]
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [BitVec.getLsbD_append (x := sign ++ exponent) (y := significand),
      BitVec.getLsbD_append (x := sign) (y := exponent)]
    intro h
    simp_all
  · constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i
      simp [BitVec.getLsbD_append (x := sign ++ exponent) (y := significand),
        BitVec.getLsbD_append (x := sign) (y := exponent)]
      intro h
      have hnot : ¬ 52 + i < 52 := by omega
      simp_all
    · apply BitVec.eq_of_getLsbD_eq
      intro i
      simp [BitVec.getLsbD_append (x := sign ++ exponent) (y := significand),
        BitVec.getLsbD_append (x := sign) (y := exponent)]
      intro h
      simp_all

/-- Exact codec transport of equality-or-quiet-NaNs; no payload equality premise. -/
theorem holFloatRefines_to_fp64 {source target : HolFloat 52 11}
    (h : holFloatRefines source target) :
    fp64Refines (holFloatToFp64 source) (holFloatToFp64 target) := by
  rcases h with h | h
  · exact Or.inl (congrArg holFloatToFp64 h)
  · apply Or.inr
    simpa [holFp64IsNan, holFp64IsSignalling, fp64ToFloat_floatToFp64_exec] using h

/-- Executable binary64 add at WordSem's roundTiesToEven mode.
WordSem observes only the output word, not IEEE flags. -/
def execFp64Add (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatAddRte64 (holFp64ToFloat a) (holFp64ToFloat b))

/-- Full arbitrary-input word refinement to the actual rendered operation. -/
theorem holFp64Add_refines_exec (a b : BitVec 64) :
    fp64Refines (holFp64Add .roundTiesToEven a b) (execFp64Add a b) := by
  rw [holFp64Add_rte]
  exact holFloatRefines_to_fp64 (holFloatAddRte64_refines_exec _ _)

/-- Executable binary64 sub at WordSem's roundTiesToEven mode.
WordSem observes only the output word, not IEEE flags. -/
def execFp64Sub (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatSubRte64 (holFp64ToFloat a) (holFp64ToFloat b))

/-- Full arbitrary-input word refinement to the actual rendered operation. -/
theorem holFp64Sub_refines_exec (a b : BitVec 64) :
    fp64Refines (holFp64Sub .roundTiesToEven a b) (execFp64Sub a b) := by
  rw [holFp64Sub_rte]
  exact holFloatRefines_to_fp64 (holFloatSubRte64_refines_exec _ _)

/-- Executable binary64 mul at WordSem's roundTiesToEven mode.
WordSem observes only the output word, not IEEE flags. -/
def execFp64Mul (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatMulRte64 (holFp64ToFloat a) (holFp64ToFloat b))

/-- Full arbitrary-input word refinement to the actual rendered operation. -/
theorem holFp64Mul_refines_exec (a b : BitVec 64) :
    fp64Refines (holFp64Mul .roundTiesToEven a b) (execFp64Mul a b) := by
  rw [holFp64Mul_rte]
  exact holFloatRefines_to_fp64 (holFloatMulRte64_refines_exec _ _)

/-- Executable binary64 div at WordSem's roundTiesToEven mode.
WordSem observes only the output word, not IEEE flags. -/
def execFp64Div (a b : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatDivRte64 (holFp64ToFloat a) (holFp64ToFloat b))

/-- Full arbitrary-input word refinement to the actual rendered operation. -/
theorem holFp64Div_refines_exec (a b : BitVec 64) :
    fp64Refines (holFp64Div .roundTiesToEven a b) (execFp64Div a b) := by
  rw [holFp64Div_rte]
  exact holFloatRefines_to_fp64 (holFloatDivRte64_refines_exec _ _)

/-- Executable FMA in fpSem/WordSem order: v2*v3 + v1, with one rounding. -/
def execFp64Fma (v1 v2 v3 : BitVec 64) : BitVec 64 :=
  holFloatToFp64 (execFloatMulAddRte64 (holFp64ToFloat v2)
    (holFp64ToFloat v3) (holFp64ToFloat v1))

/-- Full FMA refinement retains the original accumulator/operand order. -/
theorem fpSemFpfma_refines_exec (v1 v2 v3 : BitVec 64) :
    fp64Refines (fpSemFpfma v1 v2 v3) (execFp64Fma v1 v2 v3) := by
  rw [fpSemFpfma_rte]
  exact holFloatRefines_to_fp64 (holFloatMulAddRte64_refines_exec _ _ _)

end Flapjack
