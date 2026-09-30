# Soundness status

Flapjack is an in-progress Lean 4 port of the CakeML Pancake compiler. This
document records what the current repository does and does not establish. It
is deliberately conservative: a theorem that elaborates and a compiler path
that runs are not, by themselves, evidence that the port is equivalent to the
HOL development or ready for production use.

## Scope

The intended target is Pancake source compiled to RISC-V. Backends other than
RISC-V are out of scope. The CakeML checkout in `cakeml` is the reference for
the ASTs, pass ordering, semantics, compiler, and correctness theorem. The
current source-facing command is documented in the repository README and is
implemented by `Flapjack.CompileMain`.

## What is currently checked

- Lean checks the definitions and proof terms that are present in the tree.
- The repository builds with `lake build Flapjack.lean`.
- `lake test` runs executable regression tests for selected parser, lowering,
  linked-image, and RISC-V encoding cases.
- Selected pass-local theorems cover small source, allocation, Stack, and
  RISC-V fragments. Their statements have not received an independent
  correspondence review against HOL.
- The source-facing compiler reports parse, static-check, entry-point, and
  lowering failures instead of silently treating every unsupported construct as
  compiled code. The default CLI artifact is Pancake-compatible RISC-V
  assembly; `--hex` is an explicitly named compatibility mode for the historical
  raw byte line.

These checks establish useful local properties of the covered fragments. They
do not establish whole-compiler equivalence.

## HOL-to-Lean trust boundary

This project ports HOL definitions and theorem statements into Lean; it does
not prove, and currently cannot prove within either prover, that a HOL
definition and its Lean translation are equivalent. Such a cross-prover
equivalence proof is out of scope. A `@[hol]` tag is applied only after review
of the source and Lean declaration shapes; it records reviewed provenance,
not a machine-checked equivalence certificate. Confidence in a
translation comes from line-by-line review of definitions and theorem shapes,
direct HOL probes compared with Lean results, and differential compiler tests.
Those checks are valuable but finite and do not close this trust boundary.

`HOL-THEOREM-MAP.json` records each tagged declaration and every theorem or
lemma under `Flapjack/Pancake/Proofs`, including statement-review status and a
reviewer field. The CI gate checks inventory coverage and metadata consistency;
it does not perform statement review. Entries marked
`pending_statement_review` or `no_hol_reference_pending_classification` remain
open review work and must not be described as exact HOL ports. A `reviewer`
field on a pending entry records inventory authorship, not completed statement
review.

Lean proofs establish their conclusions about the Lean definitions actually
used in their statements. Even a complete Lean port of Pancake's correctness
chain would imply a property of the original HOL/Pancake compiler only under
the externally reviewed assumption that the relevant definitions and theorem
statements were translated faithfully.

## Explicit limitations

The following are open review or verification obligations:

1. Flapjack has no assembled top-level Pancake compiler-correctness theorem for
   the whole source-to-RISC-V compiler. The `pc_compile_correct`
   pass-simulation chain has since been ported
   (`Flapjack/Pancake/Proofs/PanToCrep/PcCompileCorrect/Assembly.lean`), but it
   is not yet composed with the remaining lowerings into an end-to-end
   statement. `Flapjack/PanToCrepCorrectnessBoundary.lean` contains only
   elementary value-context and non-overlap facts; it is not a compiler
   correctness boundary. Therefore the current lower-level theorems do not
   imply soundness or semantic preservation for the whole source-to-RISC-V
   compiler.
2. The RISC-V semantics in Flapjack have not yet been compared systematically
   with the Sail RISC-V model. The HOL reference model is available at
   `/home/zksecurity/HOL/examples/l3-machine-code/riscv/model/riscv.sml` in the
   development environment, but correspondence to Sail is not claimed here.
3. Compiler behavior has not been tested extensively against the original
   Pancake compiler. The executable parity suite and differential fuzzer cover
   only a small corpus and do not establish equivalence for arbitrary input.
   This limitation applies to internal and intermediate regression tests as
   well: a test that compares two Lean definitions is not evidence of Pancake
   equivalence. New porting tests must use an original CakeML executable run
   or an original HOL EVAL/probe, and record the exact source definition,
   fixture, comparison boundary, and regeneration command.
4. The compiler does not yet cover every Pancake construct or emit the same
   complete runtime/ELF artifacts as CakeML. The current command emits a
   Pancake-shaped checked RV64I assembly image for its supported source subset;
   `--hex` is the raw-byte compatibility view.
5. Proof work remains for the full source-to-target simulation, runtime image,
   collector/frame-machine behavior, calls and FFI in all configurations, and
   the complete Pancake correctness theorem.
6. Passing `lake build`, `lake test`, or CI proves only the checked repository
   state and selected regressions. It does not review the mathematical
   adequacy of the specifications or prove untested source programs compile
   identically to CakeML.
7. HOL's `panSem$evaluate_decls` now has a faithful Lean definition,
   `evaluateDecls`, checked against direct HOL probes. The distinct
   `evalPanValueDeclarationsWithStructs` remains Flapjack-specific and is not
   used as evidence for the exact `compile_top_shape_wf` port. This work does
   not claim a cross-prover equivalence proof.
8. HOL's floating-point library specifies rounding over real numbers. The
   current Lean binary64 arithmetic rendering uses `Rat` for finite float
   values and rational operation inputs. Lean proves its computable
   round-to-nearest-even algorithm agrees with the Lean choice-based
   specification for every rational input, but the correspondence between
   that rational rendering and HOL's real-number specification is a
   source-reviewed external assumption, not a kernel-checked cross-prover
   theorem. The value-component theorems do not establish flag equivalence;
   NaN payload choice remains unspecified. HOL `real_to_float` and
   `real_to_fp64` accept arbitrary reals. Lean renders them only for
   rational inputs (`holRealToFloat`, `holRealToFp64`), and there is no
   general-real result. The one wordSem use, `int_to_fp64`, applies them to
   integers, which are in scope. Irrational square-root rounding
   is not covered by these rational-input theorems, and is handled
   separately below.

   `float_sqrt` rounds the real `sqrt r` of a nonnegative rational `r`.
   `Flapjack/Misc/BinaryIeeeSqrt.lean` replaces each HOL comparison against
   `s = sqrt r` with an exact rational criterion:
   - `s ≤ q` iff `0 ≤ q ∧ r ≤ q²`;
   - `s < q` iff `0 < q ∧ r < q²`;
   - `q ≤ s` iff `q ≤ 0 ∨ q² ≤ r`;
   - `q < s` iff `q < 0 ∨ q² < r`;
   - `q = s` iff `0 ≤ q ∧ q² = r`;
   - `|A − s| ≤ |B − s|` iff `A = B`, or `A < B ∧ s ≤ (A+B)/2`, or
     `B < A ∧ (A+B)/2 ≤ s`;
   - `|s| = s`.

   `Misc/BinaryIeeeSqrt/RealAgreement.lean` now kernel-checks the rational-cut
   comparisons against Mathlib's `Real.sqrt`, including distance comparisons.
   The agreement of that Lean real specification with HOL's
   real specification remains an external assurance assumption, and this
   sqrt specification is not an exact `@[hol]` port. Lean proves that the
   computable binary64 sqrt equals the cut specification for every rational
   `r ≥ 0` (`holFloatRoundSqrt_rte_fp64`).

   HOL's rounding specification (`float_round_with_flags`, `float_round`,
   `round`, `closest_such`, `is_closest`, `threshold`) inspects its real
   argument only through order, equality and absolute-difference comparisons
   with rationals, including the flag computations, and its rounded value does
   not depend on HOL's choice operator. So the rational and rational-cut
   renderings are a representation of HOL's reals rather than a different
   specification. Every tagged declaration that uses them directly carries
   the `(reals_as_rational_cuts)` qualifier (AGENTS.md): the wordSem
   `inst_def` and the `fpSem` `fp_uop_comp_def`, `fp_bop_comp_def`,
   `fpfma_def`, `fp_cmp_comp_def` and `fp_cmp_def` renderings.
   Declarations stated over those, such as the wordSem `evaluate_def` and
   its theorems, record the inherited assumption in the theorem map
   (`inherits_reals_as_rational_cuts`, checked against a constant-closure
   export). That marker propagates the assumption only; it does not review
   the untagged definitions on the path. The qualifier is a reviewed
   representation, not an equivalence theorem, and does not remove the
   external assumption stated above.

   Every real value these renderings reach is rational except `sqrt r`:
   finite comparisons, the sum, difference, product and nonzero quotient of
   two float values, the fused `x * y + z`, `float_to_int`'s floor, ceiling
   and comparison with `1/2`, and `int_to_fp64` of an integer. Subnormal
   values are dyadic rationals, signed zeros and infinities are decided by
   sign bits and case splits without reals, the value-level `fp64_*`
   operations discard the flags, and no transcendental function is reached.
   NaN results are HOL's choice `float_some_qnan`, rendered by
   `Classical.epsilon` over the same predicate; their payload is unspecified
   in both systems, and this choice rendering is not covered by the
   qualifier.

## Trust and reproducibility notes

The normal Lean kernel checks theorem elaboration. Some existing concrete
regressions use `native_decide`; their locations are audited by
`scripts/check-native-decide.sh` and the allowlist. This is a repository
engineering policy and should not be confused with an independent review of
the theorem statements or a proof of semantic equivalence to HOL.

The authoritative reference sources remain under `cakeml/pancake`, including
`pan_to_targetScript.sml` and its proof files. When adding a parity fixture,
record the source program, the exact reference command/output boundary, and
any normalization of labels or names. A fixture that fails against CakeML is a
compiler-parity bug and must remain tracked as high-priority work until fixed
or its reference interpretation is corrected.

The checked-in HOL probes under `scripts/hol-probes` provide the same evidence
for intermediate definitions that cannot be observed through the source
compiler command. They are optional for normal Lean builds, but their outputs
must be regenerated from the original CakeML/HOL source before the associated
porting bead is closed.

## Required next evidence for a stronger claim

Before describing Flapjack as a Pancake-equivalent compiler, the project needs
all of the following:

- an independently reviewed mapping of each ported theorem statement to its
  HOL counterpart;
- systematic RISC-V semantic comparison against the Sail model for the
  instructions and machine state used by the backend;
- differential tests over a substantially representative Pancake corpus,
  comparing parse results, intermediate programs, and final artifacts with
  documented name/label normalization;
- completed source-to-RISC-V and runtime-image correctness proofs for the
  supported RISC-V configuration; and
- explicit coverage/error behavior for every remaining unsupported construct.
