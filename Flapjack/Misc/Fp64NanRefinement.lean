import Flapjack.Misc.MachineIeee
import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeRound

/-!
# Refinement relation for the unspecified HOL quiet NaN at binary64

HOL `float_some_qnan` (`binary_ieeeScript.sml:495-499`) is a Hilbert choice of
*some* quiet NaN whose bit pattern is left unspecified.  The Lean rendering
`Flapjack.holFloatSomeQnan` (`Flapjack/Misc/BinaryIeeeRound.lean:178`) is the
corresponding `Classical.epsilon`, so it is noncomputable and not
bit-determined.  An executed implementation must instead produce a concrete
quiet NaN, e.g. the canonical `0x7FF8000000000000`.

This module supplies the data every such executable connection needs, as
untagged HOL standard-library infrastructure (no CakeML source declaration
lives here, so there is no `@[hol]` tag):

* `holFp64IsNan` / `holFp64IsSignalling`: the `fp64` lifts of the HOL
  `float_is_nan` / `float_is_signalling` predicates;
* `defaultQuietNan` and `defaultQuietNanFloat`: canonical concrete quiet NaNs
  at the `BitVec 64` and `HolFloat 52 11` carriers;
* `holFloatSomeQnan_isQuiet`: the chosen `float_some_qnan` result is a quiet
  (non-signalling) NaN, extracted from the `Classical.epsilon` specification;
* `fp64Refines` / `holFloatRefines`: the NaN-insensitive refinement relation
  "equal, or both quiet NaNs with possibly different payloads", used to state
  the executable agreement without claiming bit-equality on NaN results.

The relation states arithmetic-result agreement without presupposing a target
run. It does not establish whole WordSem observational agreement: the literal
`FPMovToReg` clause at `wordSemScript.sml:889-896` exposes all 64 bits, or
both 32-bit halves, through integer registers. Distinct related quiet NaNs can
therefore yield distinct integer observations. The counterexamples below pin
this limitation; an observation-safe choice/refinement policy remains a
prerequisite of the executable evaluator connection (bead `flapjack-s7o5`).
They do not assert that HOL's chosen NaN differs from the canonical value.
-/

namespace Flapjack

/-- HOL `float_is_nan` lifted to `fp64` through `fp64_to_float`. -/
def holFp64IsNan (a : BitVec 64) : Bool :=
  holFloatIsNan (holFp64ToFloat a)

/-- HOL `float_is_signalling` lifted to `fp64` through `fp64_to_float`. -/
def holFp64IsSignalling (a : BitVec 64) : Bool :=
  holFloatIsSignalling (holFp64ToFloat a)

/-- The canonical quiet NaN at binary64: all-ones exponent and a significand
    whose most significant bit is set (so it is not signalling). -/
def defaultQuietNan : BitVec 64 := 0x7FF8000000000000

/-- The same canonical quiet NaN at the `HolFloat 52 11` carrier. -/
def defaultQuietNanFloat : HolFloat 52 11 :=
  { sign := 0, exponent := BitVec.allOnes 11, significand := BitVec.ofNat 52 (2 ^ 51) }

/-- `defaultQuietNan` is a quiet (non-signalling) NaN. -/
theorem defaultQuietNan_isQuiet :
    holFp64IsNan defaultQuietNan = true ∧ holFp64IsSignalling defaultQuietNan = false := by
  decide +kernel

/-- `defaultQuietNanFloat` is a quiet (non-signalling) NaN. -/
theorem defaultQuietNanFloat_isQuiet :
    holFloatIsNan defaultQuietNanFloat = true ∧
      holFloatIsSignalling defaultQuietNanFloat = false := by
  decide +kernel

/-- The HOL unspecified quiet NaN is a quiet (non-signalling) NaN: the
    `Classical.epsilon` selection returns a value satisfying its predicate,
    witnessed by the canonical quiet NaN. -/
theorem holFloatSomeQnan_isQuiet (fpOp : HolFpOp 52 11) :
    holFloatIsNan (holFloatSomeQnan fpOp) = true ∧
      holFloatIsSignalling (holFloatSomeQnan fpOp) = false :=
  Classical.epsilon_spec
    (p := fun f : HolFpOp 52 11 → HolFloat 52 11 =>
      holFloatIsNan (f fpOp) = true ∧ holFloatIsSignalling (f fpOp) = false)
    ⟨fun _ => defaultQuietNanFloat, defaultQuietNanFloat_isQuiet⟩

/-- NaN-insensitive refinement at binary64: the two results are either
    bit-equal, or both quiet NaNs with possibly different payloads. -/
def fp64Refines (hol exec : BitVec 64) : Prop :=
  hol = exec ∨
    (holFp64IsNan hol = true ∧ holFp64IsNan exec = true ∧
      holFp64IsSignalling hol = false ∧ holFp64IsSignalling exec = false)

/-- NaN-insensitive refinement at the `HolFloat 52 11` carrier. -/
def holFloatRefines (hol exec : HolFloat 52 11) : Prop :=
  hol = exec ∨
    (holFloatIsNan hol = true ∧ holFloatIsNan exec = true ∧
      holFloatIsSignalling hol = false ∧ holFloatIsSignalling exec = false)

/-- The HOL unspecified quiet NaN refines the canonical concrete quiet NaN:
    the two differ only in payload, which the relation ignores. -/
theorem holFloatSomeQnan_refines_defaultQuietNanFloat (fpOp : HolFpOp 52 11) :
    holFloatRefines (holFloatSomeQnan fpOp) defaultQuietNanFloat :=
  Or.inr ⟨(holFloatSomeQnan_isQuiet fpOp).1, defaultQuietNanFloat_isQuiet.1,
    (holFloatSomeQnan_isQuiet fpOp).2, defaultQuietNanFloat_isQuiet.2⟩

/-- `fp64Refines` holds for `defaultQuietNan` against itself. -/
theorem defaultQuietNan_refines_self : fp64Refines defaultQuietNan defaultQuietNan :=
  Or.inl rfl

/-- Flapjack-specific counterexample to bitcast preservation by `fp64Refines`.
There is no HOL theorem being ported here. The two concrete quiet NaNs satisfy
our arithmetic-result relation, while the RV64 `FPMovToReg` word conversion
and its other-width low-half extraction distinguish their payloads. This does
not determine the value selected by HOL's unspecified quiet-NaN choice. -/
theorem fp64Refines_distinctBitcastCounterexample :
    fp64Refines (0x7FF8000000000001 : BitVec 64) defaultQuietNan ∧
    (0x7FF8000000000001 : BitVec 64).setWidth 64 ≠ defaultQuietNan.setWidth 64 ∧
    (0x7FF8000000000001 : BitVec 64).extractLsb 31 0 ≠
      defaultQuietNan.extractLsb 31 0 := by
  constructor
  · apply Or.inr
    decide +kernel
  · decide +kernel

/-- Flapjack-specific impossibility result: the arithmetic NaN relation alone
cannot imply equality of all RV64 bitcast observations. Whole-evaluator
routing needs a justified observation policy beyond this relation. -/
theorem fp64Refines_not_preserveBitcast :
    ¬ (∀ a b : BitVec 64, fp64Refines a b → a.setWidth 64 = b.setWidth 64) := by
  intro h
  exact fp64Refines_distinctBitcastCounterexample.2.1
    (h _ _ fp64Refines_distinctBitcastCounterexample.1)

end Flapjack
