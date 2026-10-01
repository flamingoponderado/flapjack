# Native limit-var routing audit: corrected allocator boundary

This report supersedes the discovery-only measurements from `de88e014e`.
The original benchmark used `wordFfiDiscoveryBody`, which also runs DCE and
unreachable removal. Actual allocation receives the selected program before
those discovery-only transformations. The earlier 23/31 ms figures therefore
did not measure the actual allocator input.

The compiler callers and benchmark now share `wordBeforeSsaAllocatorBody`:
`wordInstSelectProgramFrom (wordToWordPreSsa (wordFlattenProgramFrom body))`.
Its kernel-checked equation is identical to the original inline preparation.
All three executed allocator callers use it; FFI discovery applies its existing
DCE/unreachable passes afterwards. Compiler behavior and oracle manifests are
unchanged.

## Corrected results

| Actual allocator inputs | Functions | Direct limit per pass | Codec plus native limit per pass | Added time |
|---|---:|---:|---:|---:|
| 166 corpus entries (161 files) | 863 | 0.290 ms | 2.187 ms | 1.897 ms |
| Pinned accelerated guest | 823 | 16.464 ms | 31.849 ms | 15.385 ms |
| Pinned software guest | 805 | 18.143 ms | 35.822 ms | 17.678 ms |

The manifest contains five repeated source entries; all 166 entries were retained.
Every function invocation was checked: zero codec rejections, zero value mismatches, and
matching observed direct/native checksums throughout. Three fresh full compiler
runs per guest preserved the exact pinned original stdout hashes. Complete
compile medians were 13.877 s and 31.448 s. The additional cost of one helper
sweep is about 0.111% and 0.056% of those times. These measurements establish
no material performance exception; actual native routing remains open.

The scope mistake changes observed limits, not just a label: the
`pxn98_unreach_elim.pnk` checksum is 23 at the actual allocator boundary versus
19 after discovery cleanup. The accelerated guest checksum is 29815 versus
29771; software is 30381 on both. Old captures are retained unchanged under
`discovery-superseded/`, with an explicit correction of their scope. Comparing
timing differences between these captures does not isolate a speed change:
input shape and shared-host load differ.

## Method and scope

The source frontend follows parser/static checking, default-main handling,
Pan simplification/structuring, global/Crep compilation, the source Loop route,
and actual `panToWordCompileProg`. Each Word function is then prepared by the
same helper called immediately before the production allocator. Preparation is
outside helper timing. Native measurements encode the complete actual program
and call reviewed `WordAlloc.limitVar`; direct measurements call the actual
`wordSsaLimitVar` helper.

The compiled helpers are marked `noinline`. Both paths are warmed; paired order
alternates; every result feeds a printed checksum; native projection is
recomputed on every call. Corpus totals use five samples with 20 repetitions,
divided by 20 before summing across all 166 corpus entries. Guests use five samples with
five repetitions. The table gives each path median separately. The host is
shared and has no exclusive CPU affinity; raw samples expose variation.
Full-compile timing includes process startup and captured output.

`wordSsaLimitVar_codec` proves actual helper correspondence for arbitrary
formals, positive widths and every production program at the Option level.
`wordBeforeSsaAllocatorBody_eq` checks the whole preparation equation without
an allocation-success premise. Empirical coverage does not establish universal
pre-SSA codec preservation. This is not an end-to-end timing of a compiler
already rerouted through native limit; call frequency and other inputs can
change total cost. Source codec closure and actual native caller wiring remain
tracked on the open routing dependency graph.

## Reproduce

Build with `lake build flapjack-limit-var-bench flapjack-compile`, then run:

```sh
python3 scripts/benchmark-native-limit-var.py --corpus --repeats 20 --samples 5
python3 scripts/benchmark-native-limit-var.py --repeats 5 --samples 5 \
  /tmp/flap-03rs-ci-fetch/guest.pp.pnk \
  /tmp/flap-03rs-ci-fetch/guest-software.pp.pnk
```

Raw JSONL files contain every coverage record and timing sample, including any
failures. A rejection/mismatch causes a nonzero exit. `metadata.json` pins all
163 distinct input-file hashes for 168 invocations and the raw captures, toolchain, baseline and corrected
measurement boundary. `full-guests.jsonl` contains all six fresh complete
compiler timing/output-hash samples. The commit containing this report pins
the benchmark and production preparation code; the metadata baseline is the
ordinary-merged tree before this repair.
