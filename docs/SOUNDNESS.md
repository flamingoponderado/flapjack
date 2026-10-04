# Soundness status

This list is not exhaustive. Items are added occasionally as they
are noted down rather than as a complete inventory of every open question.

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

Similarity to HOL artifacts does not establish equivalence. HOL-to-Lean
equivalence proofs are out of scope; `@[hol]` tags record reviewed provenance,
not equivalence certificates. Lean proofs establish results only about the
Lean definitions in their statements. Those definitions, statements, and their
implications must be evaluated independently of the HOL artifacts; HOL's
assurance does not automatically transfer to Flapjack.

The translation of HOL's choice operators is also an external assumption.
`holOptionSome` and `buildLprefixLub` use Lean's classical choice; in particular,
no cross-language agreement is established for choices on non-chain prefix
families. These already-present definitions do not add a new Lean trust root,
but kernel-checked wrapper theorems do not resolve this translation assumption.

## Explicit limitations

The following are open review or verification obligations:

1. The source-to-RISC-V theorem chain and its connection to the default compiler
   have been ported. Their statements, assumptions, and implications still
   require independent review.
2. The RISC-V semantics in Flapjack differ from the authoritative Sail RISC-V
   model. Users should review Flapjack's RISC-V semantics
   (`Flapjack.RiscV.L3`, a port of the HOL4 L3 RISC-V model) before relying
   on the compiler. The correctness theorem is stated against that model
   through `riscvNext`, not against Sail. Flapjack's `main` branch tries to
   follow the original Pancake compiler's choices about RISC-V semantics,
   including its use of the L3 model. Where L3 and Sail differ, `main` keeps
   the L3 behaviour instead of changing the model to match Sail.

   The separate project
   [flapjack-riscv-check](https://github.com/flamingoponderado/flapjack-riscv-check)
   (at commit `20c1d8e`, which pins Flapjack `0496e86c3`) compares the two
   models in Lean against `LeanRV64D`, the Lean extraction of the Sail model.

   That project proves a simulation from L3 steps to Sail steps (`step_sim`
   and `run_sim`). The simulation holds only under the following
   restrictions. Outside them, the models are known to diverge or have not
   been compared:

   - **Instructions.** It covers only the 37 instructions that `riscvEnc`
     emits: LUI, AUIPC, ADDI, ORI, XORI, ANDI, ADD, SUB, AND, OR, XOR, SLTU,
     SLLI, SRLI, SRAI, SLL, SRL, SRA, DIV, MUL, MULHU, LD, LWU, LHU, LBU, SD,
     SW, SH, SB, BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL and JALR.
   - **Hint encodings.** Sail decodes `ADD x0, x0, x2..x5` as a Zihintntl
     `NTL` hint. It decodes `ORI x0, rs1, imm` with `imm[4:0] ∈ {0,1,3}` as a
     Zicbop prefetch, which probes PMA/PMP. L3 decodes both as ordinary ALU
     operations writing `x0`. These encodings are excluded.
   - **Misaligned loads and stores.** L3 performs them. Sail traps or splits
     them depending on the PMA region. All accesses are assumed aligned.
   - **Memory.** L3's `MEM8` is total. Sail's memory is a partial map with
     PMA regions and MMIO windows (CLINT, signature, HTIF). Fetches, loads
     and stores must lie in a suitable RAM region, miss the MMIO windows,
     and stay within the related memory domain.
   - **Sail configuration.** The following are fixed as invariants:
     - machine mode with `mstatus.MPRV = 0`;
     - pointer masking off and every PMP entry OFF;
     - `misa.C = misa.M = 1`;
     - `mseccfg.MLPE = 0` and `elp = 0` (otherwise Sail's JALR updates
       Zicfilp landing-pad state, which L3 does not model);
     - `mstatus.MIE = 0`, so there are no interrupts;
     - a 4-aligned PC.
   - **Not compared.** Floating point is not compared, because every Sail
     floating-point primitive is an uninterpreted `axiom`. Also not compared:
     CSRs, traps, privilege changes and virtual memory (L3 follows the old
     privileged spec 1.7), atomics, and RV64IM instructions outside the set
     above. The cycle and instret counters are not related.

   The compiler correctness theorem has not been transferred to Sail. That
   needs a Sail-based machine configuration and a proof that every execution
   of compiled code meets the side conditions above. The code must be
   hint-free encodings of the covered instructions, every access must be
   aligned plain RAM in the related domain, and the PC must stay 4-aligned.
   Neither has been done. The comparison is also not a proof that L3 and
   Sail are equivalent: only the L3-to-Sail direction is proved, and only on
   the restricted fragment.
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
   Pancake-compatible RISC-V assembly, including M-extension multiplication and division;
   `--hex` is the raw-byte compatibility view.
5. The ported correctness results retain explicit source, machine, installation,
   FFI, and resource premises. They do not establish correctness of every driver
   mode, parser behavior, runtime installation, or configuration.
   The theorem concerns `parsed.map declToHOL`: the parser and `declToHOL`
   are trusted. It requires a `main` function and source premises such as
   `good_code` and distinct parameters; compilation does not check all these
   premises. No witness establishes that the machine, memory-layout and
   `panInstalled` premises are jointly satisfiable, so vacuity remains a risk.
   Assembly rendering and startup code are also trusted: the output theorem
   identifies a rendering of the compiled tuple, but does not prove that the
   assembly frame emits those bytes or establishes installation. Only `--hex`
   directly renders `hexBytes bytes`.
6. Passing `lake build`, `lake test`, or CI proves only the checked repository
   state and selected regressions. It does not review the mathematical
   adequacy of the specifications or prove untested source programs compile
   identically to CakeML.
8. HOL's floating-point library specifies rounding over real numbers. The
   current Lean binary64 arithmetic rendering uses `Rat` for finite float
   values and rational operation inputs. Lean proves its computable
   round-to-nearest-even algorithm agrees with the Lean choice-based
   specification for every rational input, but the correspondence between
   that rational rendering and HOL's real-number specification is a
   source-reviewed external assumption, not a kernel-checked cross-prover
   theorem. The value-component theorems do not establish flag equivalence;
   NaN payload choice remains unspecified. HOL `real_to_float` and
   `real_to_fp64` accept arbitrary reals. The executed path renders them
   only for rational inputs (`holRealToFloat`, `holRealToFp64`); the
   general-real `real_to_float` over Mathlib `ℝ` is `holRealToFloatR`, and
   `holRealToFloatR_ratCast` proves that at every rational argument it equals
   the executed `holRealToFloat` (likewise `round`, `float_round` and
   `float_round_with_flags`, in `Flapjack/Misc/BinaryIeeeSqrt/RealCarrier.lean`).
   The one wordSem
   use, `int_to_fp64`, applies them to integers, which are in scope. The
   WordSem and StackSem `FPSqrt`/`FPToInt`/`FPFromInt` instruction clauses
   are proved equal, with no premise, to the same clauses over the tagged
   Mathlib-real `fp64_sqrt`, `fp64_to_int` and `real_to_fp64` ports
   (`WordSem/Inst/RealSqrtAgreement.lean`, `WordSem/Inst/RealConvertAgreement.lean`,
   `StackSem/FpRegisterInstructions/RealAgreement.lean`). Likewise the executed
   `float_add`/`float_sub`/`float_mul`/`float_div`/`float_mul_add`/`float_compare`
   and their generated fp64 lifts and comparisons are proved equal, for every mode
   and input, to literal Mathlib-real transcriptions
   (`Misc/BinaryIeeeArith/RealCarrier.lean`, `Misc/MachineIeee/ArithReal.lean`), so
   no executed binary64 operation relies on an unproved `Rat`-versus-real step; the
   reading of Mathlib `ℝ` as HOL `real` remains the standard carrier assumption.
   Irrational square-root rounding
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
   comparisons against Mathlib's `Real.sqrt`, including distance comparisons,
   and `Misc/BinaryIeeeSqrt/RealCarrier.lean` (with `Misc/MachineIeee/SqrtReal.lean`
   for `fp64_sqrt`) kernel-checks that the executed
   cut `float_sqrt`/`fp64_sqrt` equal literal transcriptions of HOL `round`,
   `float_round`, `float_round_with_flags` and `float_sqrt` over Mathlib `ℝ`
   (with `Real.sqrt`, HOL `abs` and all flag tests kept), for every rounding
   mode and input.
   The agreement of that Lean real specification with HOL's
   real specification remains an external assurance assumption. The fixed
   binary64 `holFp64SqrtR` wrapper has a source-reviewed `@[hol]` tag with
   the conservative IEEE real-representation qualifier; the generic
   zero-width-capable real helpers remain untagged. Consumer agreement proofs
   cover the actual unary evaluator and native WordSem sqrt instruction,
   including missing-register failure. These kernel equalities remove the
   cut-comparison proof gap without proving cross-assistant real equivalence. Lean proves that the
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

## Stack bounds and liveness

Compiler correctness does not unconditionally preserve source liveness on a
finite-memory RISC-V machine. HOL's `pan_to_target_compile_semantics`
(`cakeml/pancake/proofs/pan_to_targetProofScript.sml`) gives a precise
source-behavior guarantee only when the statically computed `stack_max` is
known and strictly below the available stack limit. `compile_prog_max` computes
that bound from frame sizes and the call graph; an unknown bound (`NONE`)
does not satisfy the condition.

Otherwise, the theorem uses `extend_with_resource_limit'`: the target may
terminate with `Resource_limit_hit` after a prefix of the source's I/O trace,
even when the source would continue or terminate normally. In particular,
recursive Pancake programs whose stack usage cannot be statically bounded can
exhaust the target stack. The theorem is therefore not an exact liveness or
complete-trace preservation guarantee for such programs; it permits RISC-V
resource exhaustion. Recursion alone is not a proof of exhaustion, and a known
bound must also fit the configured stack. A faithful Lean port must retain
this distinction, not silently strengthen the theorem to exclude out-of-memory
behavior. The assembled theorem retains this resource-limit condition.

## Trust and reproducibility notes

The Lean kernel checks elaborated theorem statements and proof terms.
Elaboration adds implicit arguments, inferred types, and resolved notation
not explicit in the source; the resulting statement may differ from what
the author intended. Some existing concrete
regressions use `native_decide`; their locations are audited by
`scripts/check-native-decide.sh` and the allowlist. This is a repository
engineering policy and should not be confused with an independent review of
the theorem statements or a proof of semantic equivalence to HOL.

## The correctness theorem cannot be summarized faithfully

The compiler correctness theorem is the top-level source-to-target result. Its
statement is large by construction: it names every definition the result
recursively depends on — the parser, lowering, the abstract CakeML semantics,
each compiler pass, the RISC-V machine semantics, the assembly rendering, and
the machine, memory-layout, and resource premises. Reading the statement
therefore means following every one of those definitions; the statement is not
a short claim but the whole ported development written out.

No natural-language summary of the theorem is accurate. Every paraphrase,
including the ones in this document and in commit messages, issue trackers, and
beads, omits or simplifies something the kernel actually checks, and can mislead
a reader who trusts the prose instead of the statement. Treat such summaries as
pointers to the theorem, never as the theorem itself.

To know what Flapjack actually proves, read the Lean statement and confirm that
the kernel checks it. `lake build` and `lake test` show only that a statement
elaborates and its proof term type-checks; neither reviews whether the
elaborated statement is the result its author intended, whether it matches the
HOL original, or whether the statement is what the reader wants. See
"Trust and reproducibility notes" for how elaboration can expand the written
statement beyond what the author typed.

## Required next evidence for a stronger claim

Before describing Flapjack as a Pancake-equivalent compiler, the project needs
all of the following:

- an independently reviewed mapping of each ported theorem statement to its
  HOL counterpart;
- transfer of the compiler correctness theorem to the Sail RISC-V model. The
  L3-to-Sail step and run simulation for the backend's instructions exists
  (item 2). What remains is a Sail-based machine configuration and a proof
  that compiled code meets the simulation's side conditions: hint-free
  encodings, aligned plain-RAM accesses, and a 4-aligned PC;
- differential tests over a substantially representative Pancake corpus,
  comparing parse results, intermediate programs, and final artifacts with
  documented name/label normalization;
- validation of the ported source-to-RISC-V theorem's assumptions, and proofs
  connecting assembly rendering and runtime installation to its premises; and
- explicit coverage/error behavior for every remaining unsupported construct.
