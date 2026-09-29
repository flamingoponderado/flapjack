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
    constructor maps to the corresponding `machine_ieee` `fp64_*` predicate. -/
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
    `Flapjack.Opb`; HOL `word64` is `BitVec 64`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_cmp_def"]
noncomputable def fpSemFpCmp : Opb → BitVec 64 → BitVec 64 → Bool
  | .lt => holFp64LessThan
  | .leq => holFp64LessEqual
  | .gt => holFp64GreaterThan
  | .geq => holFp64GreaterEqual

/-- Exact HOL `fp_uop_comp_def` (`fpSemScript.sml:43-49`): `FP_Sqrt` uses
    `roundTiesToEven`, the other two are sign operations. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"]
noncomputable def fpSemFpUopComp : FpUop → BitVec 64 → BitVec 64
  | .abs => holFp64Abs
  | .neg => holFp64Negate
  | .sqrt => holFp64Sqrt .roundTiesToEven

/-- Exact HOL `fp_bop_comp_def` (`fpSemScript.sml:51-58`): all four binary
    operations use `roundTiesToEven`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_bop_comp_def"]
noncomputable def fpSemFpBopComp : FpBop → BitVec 64 → BitVec 64 → BitVec 64
  | .add => holFp64Add .roundTiesToEven
  | .sub => holFp64Sub .roundTiesToEven
  | .mul => holFp64Mul .roundTiesToEven
  | .div => holFp64Div .roundTiesToEven

/-- Exact HOL `fpfma_def` (`fpSemScript.sml:60-62`):
    `fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`, so the first
    argument is the addend.  HOL `word64` is `BitVec 64`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fpfma_def"]
noncomputable def fpSemFpfma (v1 v2 v3 : BitVec 64) : BitVec 64 :=
  holFp64MulAdd .roundTiesToEven v2 v3 v1

/-- Exact HOL `fp_top_comp_def` (`fpSemScript.sml:64-66`): `fp_top_comp fop =
    fpfma`, i.e. the construction ignores `fop`. -/
@[hol "cakeml/semantics/fpSemScript.sml" "fp_top_comp_def"]
noncomputable def fpSemFpTopComp : FpTop → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 :=
  fun _ => fpSemFpfma

end Flapjack
