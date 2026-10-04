# Flapjack

The persistent `riscv-mi` branch specializes Flapjack for the integer RISC-V
target described by the sibling `riscv-zkvm` repository. `main` continues the
port close to the original CakeML/HOL development; changes specific to this
branch should stay on `riscv-mi` rather than merge back into `main`.
The reference repositories `riscv-zkvm`, `cakeml`, and `HOL` are read-only.

This branch removes floating-point language operations, privileged returns,
hardware timers and interrupts, and instructions that enable page tables.
Compiler evaluation fuel is distinct from hardware time. Integer compiler
passes and their applicable reference tests remain part of the build.
Reduced definitions are branch-specific specifications, not exact ports of
the full HOL definitions.

> **Warning — work in progress.** Nothing in this repository is ready to be
> relied upon. Do not use Flapjack for anything of value.

Flapjack is an in-progress Lean 4 port of the formally verified Pancake compiler.

- A compiler correctness theorem from Pancake to a vibe-ported RISC-V semantics
  has been proven, under explicit assumptions: [Lean theorem](https://github.com/flamingoponderado/flapjack/blob/4e120dd7303f7e66a13f04ad60404273a9d90e9c/Flapjack/Pancake/Proofs/PanToTarget/RiscVInstance.lean#L45),
  [corresponding original CakeML theorem](https://github.com/CakeML/cakeml/blob/857f0d98da8f8a3580f34423338e697809308ede/pancake/proofs/pan_to_targetProofScript.sml#L1257).
- The vibe-ported RISC-V semantics has not been validated. Comparison against
  the Lean extraction of the Sail RISC-V model is future work.
- Other backends, including ARM and x86, have not yet been ported to Lean.
- The CakeML front end has not been ported to Lean.

The Lean specifications and their implications still require independent review. See
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) for limitations and
[`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md) for reference comparisons.

## Usage

Install the pinned Lean toolchain and build the library:

```sh
lake build
```

Run the executable regression suite, including the CakeML-derived RISC-V
byte goldens:

```sh
lake test
```

Compile a Pancake source file through the source-facing RV64I path:

```sh
lake exe flapjack-compile program.pnk > program.riscv.S
```

The compiler also reads source from standard input:

```sh
printf 'fun 1 main() { return 7; }\n' | lake exe flapjack-compile
```

The default output (also selected by `--assembly` or `--pancake`) follows the
original Pancake/CakeML RISC-V assembly artifact boundary: runtime data and
bitmap framing, `cml_main` startup, `cake_main`, linked code-section labels,
`.byte` payloads, and `cake_codebuffer_*` markers. It is not an ELF file. For
the historical raw byte artifact, use:

```sh
lake exe flapjack-compile --hex program.pnk > program.riscv.hex
```

The original reference compiler can be run locally with:

```sh
cakeml/developers/bin/cake --pancake --target=riscv < program.pnk > program.cake.S
```

Use the parity tests, [`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md), and
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) when interpreting comparisons between
the two outputs. For randomized cross-checking, the deterministic
differential fuzzer `scripts/parity-difffuzz.py` compares full artifacts
(sections, bytes, frame, acceptance) against `cake` and files every unknown
mismatch as a bead; see the differential-fuzzing section of
[`docs/PARITY-TESTING.md`](docs/PARITY-TESTING.md).

For the parser API and its current limitations, see
[`Flapjack/Parser/README.md`](Flapjack/Parser/README.md).

When porting a definition or theorem, generate the local CakeML/HOL source
index with `python3 scripts/index-hol.py`. It records declaration locations,
theory dependencies, and the CakeML commit used; see
[`docs/HOL-INDEX.md`](docs/HOL-INDEX.md). The generated `.hol-index/` directory
is gitignored.
The evolving HOL-to-Lean source layout is recorded in
[`docs/HOL-LAYOUT.md`](docs/HOL-LAYOUT.md).

## Port in progress

The RISC-V compiler port and its correctness proof
are still in progress. [GitHub issues](https://github.com/pirapira/flapjack/issues)
track work and claims; [`PLAN.md`](PLAN.md) gives the staged direction.
[`docs/SOUNDNESS.md`](docs/SOUNDNESS.md) describes limitations, external
assumptions, and out-of-scope gaps.
Start with the porting and verification rules in [`AGENTS.md`](AGENTS.md).

Work bottom-up from a desired theorem through its HOL dependencies: port small
definitions and supporting lemmas first. Use `@[hol ...]` tags and
`scripts/check-hol-refs.py --mapping` to locate existing work. Run
`python3 scripts/next-hol-port.py --file cakeml/pancake/FILE.sml` to list
untagged candidates in a script; `--goal HOL_NAME` limits the list to earlier
declarations, and `--kind Theorem` includes theorem candidates. Check the
source, Lean analogues, and issue claims before choosing a target: tags are
navigation aids, not evidence of equivalence or of a missing port.

## Acknowledgements

Flapjack was started with the support of [zkSecurity](https://zksecurity.xyz)
and the [Ethereum Foundation](https://ethereum.foundation).
