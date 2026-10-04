# Legacy SmartSeq interpreter benchmark

The legacy `RiscV.wordSimpSmartSeq` retains its constant-time constructor
operation. Encoding the accumulated prefix and next statement, applying the
reviewed native `WordSimp.smartSeqHOL`, and decoding the result repeatedly
traverses the entire growing prefix. Two paired runs on real compiler-produced
sequence inputs measured 4959.50/3969.97 ms for this full-codec route versus
11.49/8.67 ms for the benchmark builder: approximately 432/458 times its cost.
These timings use `#eval` in the interpreter. The measured `wordSimpLeftSeq`
builder is used by the legacy `wordSimpSeqAssocItemsFuel`, not the native default route.
These are sequence-building measurements on this host, not whole-compiler
throughput estimates or a comparison with a shared native representation.

Reproduce from the repository root:

```sh
lake lean scripts/SmartSeqProductionProfile.lean
```

The script parses every entry of the 166-source parity corpus and runs the
physical source pipeline through its Word-function producer. It obtains the
sequence items of each function with the actual `wordSimpSeqItems`. Both runs
cover 863 functions; every complete output agrees, including nested bodies,
return/handler metadata, cutsets and instruction payloads. Encoder or decoder
rejection fails the run. Nothing is omitted to obtain a timing ratio.
`paired.csv` retains every observation; `summary.json` records aggregate
timings and the corpus hash.

Separate non-inlined IO calls bracket both builders with monotonic nanosecond
clocks. Each call forces a complete traversal of its final output; comparison
of complete renderings happens outside the clocks. Parsing and extraction are
also outside the clocks. The native alternative includes input encoding and
output decoding on every SmartSeq operation, as required by adoption through
the existing different carriers. Small individual observations are noisy;
the exception uses the paired aggregate cost. This profile measures the
top-level prefix folds, not every nested SmartSeq call in the compiler.

The relationship is kernel-checked in
`Flapjack/Compiler/Backend/WordSimp/ProductionSmartSeq.lean`:
`smartSeq_production` proves the whole actual operation's encoder result;
`smartSeqFold_production` composes every represented statement and accumulator;
`smartSeqLeftSeq_production` covers the benchmark builder, including empty and
all-Skip lists. The input encodings identify the carrier image; none assumes
the output encoding, a desired fold relation or target execution.

This exception covers the native codec image. Unsupported broader instruction
forms remain governed by the existing partial encoder; this does not turn them
into exact HOL instructions. This benchmark does not describe the default
compiler change in PR1215 or the legacy constant-propagation repair across stores.
The measurements and carrier proofs do not establish HOL-to-Lean equivalence
or complete WordSimp or whole-compiler semantic simulation.
