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
2. The RISC-V semantics in Flapjack have not been proven equivalent to a Lean
   extraction of the authoritative Sail RISC-V model.
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
8. The persistent `riscv-mi` branch removes floating-point operations and
   their IEEE/real renderings. Their rounding and real-carrier assumptions
   apply to the full development on `main`, not to this integer branch.
   Instruction and machine carriers here are reduced specifications for the
   supported `riscv-zkvm` subset. Surviving compiler proofs over those carriers
   are branch-specific results; they are not exact ports of the original
   full-HOL statements. Independent HOL declarations keep their applicable
   reference annotations. Rejection tests establish the unsupported-opcode
   boundary, not semantic equivalence with `riscv-zkvm`.

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
- systematic RISC-V semantic comparison against the Sail model for the
  instructions and machine state used by the backend;
- differential tests over a substantially representative Pancake corpus,
  comparing parse results, intermediate programs, and final artifacts with
  documented name/label normalization;
- validation of the ported source-to-RISC-V theorem's assumptions, and proofs
  connecting assembly rendering and runtime installation to its premises; and
- explicit coverage/error behavior for every remaining unsupported construct.
