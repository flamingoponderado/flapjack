import Flapjack.HolRef
import Flapjack.AstHOL
import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeSqrt

/-!
# CakeML `fpSem` operations used by wordSem

Lean counterpart of `cakeml/semantics/fpSemScript.sml` (bead
`flapjack-h29l.6.2.2`).  The `fp_cmp`/`fp_uop`/`fp_bop`/`fp_top` datatypes and
their `*_comp` interpretation functions are ported here, together with
`fp_cmp_def` (over the exact `ast$opb` carrier `Flapjack.Opb`),
`fpfma_def`, the fused multiply-add used by wordSem `inst_def`'s `FPFma` case,
over the rendered HOL `machine_ieee` `fp64_*` operations.  HOL `word64` is
`BitVec 64`.
-/

namespace Flapjack

/-- Exact HOL `fp_cmp` (`fpSemScript.sml:8-10`):
    `FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp"]
inductive FpCmp where
  | less
  | lessEqual
  | greater
  | greaterEqual
  | equal
  deriving DecidableEq, Repr

/-- Exact HOL `fp_uop` (`fpSemScript.sml:12-14`):
    `FP_Abs | FP_Neg | FP_Sqrt`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop"]
inductive FpUop where
  | abs
  | neg
  | sqrt
  deriving DecidableEq, Repr

/-- Exact HOL `fp_bop` (`fpSemScript.sml:16-18`):
    `FP_Add | FP_Sub | FP_Mul | FP_Div`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_bop"]
inductive FpBop where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

/-- Exact HOL `fp_top` (`fpSemScript.sml:20-22`): `FP_Fma`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_top"]
inductive FpTop where
  | fma
  deriving DecidableEq, Repr

/-- Exact HOL `fp_cmp_comp_def` (`fpSemScript.sml:33-41`): each comparison
    constructor maps to the corresponding `machine_ieee` `fp64_*` predicate.

    Binary64 dependency (bead `flapjack-2hoy`): the `fp64_*` comparisons are
    HOL's `float_compare` (`binary_ieeeScript.sml:758-808`) on
    `fp64_to_float`, rendered clause for clause in `Flapjack.Misc.BinaryIeee`.
    * NaN is unordered.
    * Infinities are ordered by sign.
    * `±0` compare equal (both have value `0`).
    * Finite floats compare their `float_to_real` values, which are dyadic
      rationals rendered as `Rat`.
    Agreement with HOL rests only on `ℚ → ℝ` being an ordered-field embedding
    (external assumption, `docs/SOUNDNESS.md` item 8). -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp_comp_def"]
noncomputable def fpSemFpCmpComp : FpCmp → BitVec 64 → BitVec 64 → Bool
  | .less => holFp64LessThan
  | .lessEqual => holFp64LessEqual
  | .greater => holFp64GreaterThan
  | .greaterEqual => holFp64GreaterEqual
  | .equal => holFp64Equal

/-- Exact HOL `fp_cmp_def` (`fpSemScript.sml:24-31`): `fp_cmp cmp = case cmp of
    | Lt => fp64_lessThan | Leq => fp64_lessEqual | Gt => fp64_greaterThan
    | Geq => fp64_greaterEqual`.  The argument is the `ast$opb` carrier
    `Flapjack.Opb`; HOL `word64` is `BitVec 64`.

    Binary64 dependency (bead `flapjack-2hoy`): the `fp64_*` comparisons are
    HOL's `float_compare` (`binary_ieeeScript.sml:758-808`) on
    `fp64_to_float`, rendered clause for clause in `Flapjack.Misc.BinaryIeee`.
    * NaN is unordered.
    * Infinities are ordered by sign.
    * `±0` compare equal (both have value `0`).
    * Finite floats compare their `float_to_real` values, which are dyadic
      rationals rendered as `Rat`.
    Agreement with HOL rests only on `ℚ → ℝ` being an ordered-field embedding
    (external assumption, `docs/SOUNDNESS.md` item 8). -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp_def"]
noncomputable def fpSemFpCmp : Opb → BitVec 64 → BitVec 64 → Bool
  | .lt => holFp64LessThan
  | .leq => holFp64LessEqual
  | .gt => holFp64GreaterThan
  | .geq => holFp64GreaterEqual

/-- Rendering of HOL `fp_uop_comp_def` (`fpSemScript.sml:43-49`), with the
    same case map: `FP_Abs => fp64_abs`, `FP_Neg => fp64_negate`,
    `FP_Sqrt => fp64_sqrt roundTiesToEven`.  Not an exact port: the `@[hol]`
    tag is withdrawn (bead `flapjack-2hoy.6`).  HOL `fp64_sqrt` rounds the
    real `sqrt r`, but `holFp64Sqrt` replaces each comparison against
    `sqrt r` with a rational cut criterion (`BinaryIeeeSqrt`).  That is a
    reformulation of the specification whose agreement with HOL is the
    external assumption of `docs/SOUNDNESS.md` item 8.  The faithful rendering
    is bead `flapjack-dshl`.  The `abs`/`neg` clauses are real-free sign-bit
    operations. -/
noncomputable def fpSemFpUopComp : FpUop → BitVec 64 → BitVec 64
  | .abs => holFp64Abs
  | .neg => holFp64Negate
  | .sqrt => holFp64Sqrt .roundTiesToEven

/-- Exact HOL `fp_bop_comp_def` (`fpSemScript.sml:51-58`): all four binary
    operations use `roundTiesToEven`.

    Binary64 dependency (bead `flapjack-2hoy`): the operations are HOL's
    `float_to_fp64 (SND (float_op roundTiesToEven …))`
    (`binary_ieeeScript.sml:587-722`), rendered clause for clause in
    `Flapjack.Misc.BinaryIeeeArith`.
    * The NaN, infinity, invalid and divide-by-zero branches are real-free
      and follow HOL's case order.
    * The zero-sign `toneg` choices follow HOL: equal-signed zeros for add,
      opposite signs for sub, `x.Sign ≠ y.Sign` for mul/div, and the
      `mul_add` rule.
    * The only real is the rounded argument (`r1 ± r2`, `r1 * r2`, `r1 / r2`
      with `r2 ≠ 0`, or `r1 * r2 + r3`) of dyadic float values, a rational.
    * `round`/`closest_such` quantify only over floats, with predicates built
      from `+ - * abs ≤` on those rationals.  Ties go to the even
      significand; the `±0` choice is made afterwards by `float_round`.
    * `holFloatRound_rte_fp64` proves that the rounded value is determined
      for every rational argument, so HOL's `@` and Lean's
      `Classical.epsilon` select the same float.
    * Flags are dropped as in HOL (`SND`).  NaN results are HOL's
      unspecified `float_some_qnan`, rendered by `Classical.epsilon` on the
      same predicate.
    External assumptions: `ℚ → ℝ` is an ordered-field embedding
    (`docs/SOUNDNESS.md` item 8), and HOL `@` is translated as
    `Classical.epsilon`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_bop_comp_def"]
noncomputable def fpSemFpBopComp : FpBop → BitVec 64 → BitVec 64 → BitVec 64
  | .add => holFp64Add .roundTiesToEven
  | .sub => holFp64Sub .roundTiesToEven
  | .mul => holFp64Mul .roundTiesToEven
  | .div => holFp64Div .roundTiesToEven

/-- Exact HOL `fpfma_def` (`fpSemScript.sml:60-62`):
    `fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`, so the first
    argument is the addend.  HOL `word64` is `BitVec 64`.

    Binary64 dependency (bead `flapjack-2hoy`): the operations are HOL's
    `float_to_fp64 (SND (float_op roundTiesToEven …))`
    (`binary_ieeeScript.sml:587-722`), rendered clause for clause in
    `Flapjack.Misc.BinaryIeeeArith`.
    * The NaN, infinity, invalid and divide-by-zero branches are real-free
      and follow HOL's case order.
    * The zero-sign `toneg` choices follow HOL: equal-signed zeros for add,
      opposite signs for sub, `x.Sign ≠ y.Sign` for mul/div, and the
      `mul_add` rule.
    * The only real is the rounded argument (`r1 ± r2`, `r1 * r2`, `r1 / r2`
      with `r2 ≠ 0`, or `r1 * r2 + r3`) of dyadic float values, a rational.
    * `round`/`closest_such` quantify only over floats, with predicates built
      from `+ - * abs ≤` on those rationals.  Ties go to the even
      significand; the `±0` choice is made afterwards by `float_round`.
    * `holFloatRound_rte_fp64` proves that the rounded value is determined
      for every rational argument, so HOL's `@` and Lean's
      `Classical.epsilon` select the same float.
    * Flags are dropped as in HOL (`SND`).  NaN results are HOL's
      unspecified `float_some_qnan`, rendered by `Classical.epsilon` on the
      same predicate.
    External assumptions: `ℚ → ℝ` is an ordered-field embedding
    (`docs/SOUNDNESS.md` item 8), and HOL `@` is translated as
    `Classical.epsilon`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fpfma_def"]
noncomputable def fpSemFpfma (v1 v2 v3 : BitVec 64) : BitVec 64 :=
  holFp64MulAdd .roundTiesToEven v2 v3 v1

/-- Exact HOL `fp_top_comp_def` (`fpSemScript.sml:64-66`): `fp_top_comp fop =
    fpfma`, i.e. the construction ignores `fop`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_top_comp_def"]
noncomputable def fpSemFpTopComp : FpTop → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 :=
  fun _ => fpSemFpfma

end Flapjack
