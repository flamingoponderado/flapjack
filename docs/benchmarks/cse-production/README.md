# Executed CSE performance exception

The actual allocator retains `RiscV.wordCseProp` and its `Std.TreeMap` knowledge
representation. Native source-shaped CSE is materially slower on the real
pre-CSE function inputs in the 166-entry parity corpus. Two runs measured
native CSE plus output decoding at 540.96/538.27 ms, versus executed CSE at
120.57/118.84 ms: approximately 4.5/4.5 times the pass cost. These are pass
measurements on this checkout and host, not whole-compiler throughput claims.

Reproduce from the repository root with:

```sh
lake lean scripts/CseProductionProfile.lean
```

The script parses every corpus entry and obtains the source Word functions
through the physical pipeline. It uses the actual native full-SSA metadata
producer and first `wordRemoveDeadProgramViaHOL` cleanup. Encoding/decoding
rejections and any changed input representation fail the run. Every complete
executed output and all entries of its five knowledge fields are compared with the decoded native wrapper output, including
all nested control bodies, Call return/handler payloads and cutsets. Both runs
passed for 863 functions across all 166 entries (161 distinct paths; the corpus
intentionally repeats some inputs). `paired.csv` records every function timing;
`summary.json` records aggregate totals and the corpus hash.

Separate non-inlined IO calls bracket both implementations to prevent pure
computation moving across the monotonic nanosecond clocks. Each timed call
forces a traversal of all program nodes, including both Call continuations.
Parsing, selection, SSA, first cleanup, input codecs and complete rendering
comparisons run outside the clocks. The native measurement includes decoding
its output into the representation consumed by the allocator. A native caller
would also need input encoding; its cost is excluded here, conservatively.
The earlier exploratory timings without IO barriers are superseded and are
not used to justify this exception. Small per-function timings are noisy;
the exception uses the paired aggregate totals.

The relationship is kernel-checked, rather than inferred from these fixtures.
`ProductionProgram.wordCseProgram_production_transport` relates all five
knowledge fields and the complete program.
`ProductionProgram.wordCommonSubexpElim_production_transport` relates the
complete wrapper for every represented input. It derives the output from the
existing input codec and discharges the native initial knowledge invariant.
`ProductionAllocatorInput.nativeAllocatorCse_sourceImage` derives that input
image after the actual native SSA producer and first cleanup, and then derives
the entire optimized CSE output as the projection of the original wrapper.
No roundtrip, output relation, target run or callback is assumed. Its producer
success condition is the physical metadata API condition; it does not port a
HOL pass-correctness theorem with an added successful-pass premise.

This exception covers that supported allocator source image. The separate
five-register executed AddCarry extension remains outside the original carrier;
native Skip/FP instruction forms remain rejected by the existing decoder.
The compiler does not silently translate those forms. Broader carrier and
source-to-RISC-V semantic composition remain separate open work. These runtime
comparisons and Lean carrier proofs do not establish HOL-to-Lean equivalence.
