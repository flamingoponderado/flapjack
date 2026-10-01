# Native limit-var routing audit

The native codec-and-limit path has low measured absolute cost. These measurements
provide **no material performance exception** for retaining the direct production
helper. The native routing bead remains open.

## Results

| Inputs | Functions | Direct limit per pass | Codec plus native limit per pass | Added time |
|---|---:|---:|---:|---:|
| Original 166-source corpus | 863 | 0.240 ms | 1.761 ms | 1.521 ms |
| Pinned accelerated guest | 823 | 17.472 ms | 40.454 ms | 22.982 ms |
| Pinned software guest | 805 | 26.447 ms | 57.034 ms | 30.586 ms |

Every function was checked: zero codec rejections, zero value mismatches, and
matching observed checksums throughout. Guest complete-compile medians were
13.936 s and 32.051 s, with the exact pinned original stdout hashes preserved in
all three samples. The added cost of one helper sweep is about 0.165% and 0.095%
of those times. This is a comparison of measurements, not an end-to-end benchmark
of a compiler modified to use native limit-var. Call frequency and other input
shapes can affect total cost.

Corpus totals use five paired samples with 20 repetitions, divided by 20 before
summing each sample across the 166 sources. The table reports the median total
for each path separately. Guests use five paired samples with five repetitions.
Timing runs used the compiled `flapjack-limit-var-bench` executable, performed a
warmup, alternated path order, and recomputed the native codec for every call.
The helper operations are marked `noinline`; results feed returned checksums
printed after each sample. Shared-host noise is visible in the raw samples.

## Inputs and scope

The driver follows the source parser/static checker, default-main handling,
Pan simplification and structuring, global/Crep compilation, source Loop route,
and `panToWordCompileProg`. Each function then uses `wordFfiDiscoveryBody`, the
same flattened, source-shaped pre-SSA preparation used by the production route.
Preparation is outside helper timing. Native measurements call
`wordLangProgToHOL` and reviewed `WordAlloc.limitVar` on the resulting complete
native program. Direct measurements call the actual `wordSsaLimitVar` helper.
Coverage failures are printed with indices and cause a nonzero exit.

`ProductionLimitVar.wordSsaLimitVar_codec` proves correspondence for arbitrary
formals, positive word widths, and every production program at the Option level.
It reuses the full program maximum correspondence. Both sides are `none` on codec
rejection; this does not prove that every future source program is codec accepted.
The corpus/guest coverage is empirical, not a universal source-image theorem.

The measured production SSA APIs are generic over `WordProg alpha`, while native
`limitVar` consumes a width-indexed word carrier. The remaining work is to factor
the actual initial-counter computation so the fixed-width production caller can
supply the native result, retaining generic compatibility interfaces separately,
and to prove or explicitly track source codec acceptance at that boundary.
Neither the actual compiler route nor its memory guard is changed by this audit.
No synthetic program or successful-compilation premise is used to claim routing.

## Reproduce

Build with `lake build flapjack-limit-var-bench flapjack-compile`, then run:

```sh
python3 scripts/benchmark-native-limit-var.py --corpus --repeats 20 --samples 5
python3 scripts/benchmark-native-limit-var.py --repeats 5 --samples 5 \
  /tmp/flap-03rs-ci-fetch/guest.pp.pnk \
  /tmp/flap-03rs-ci-fetch/guest-software.pp.pnk
```

The raw JSONL files contain every function-coverage record and timing sample;
`metadata.json` pins all input hashes, the raw output hashes, toolchain and host
method. `full-guests.jsonl` contains three fresh compiler wall-time/output-hash
samples per guest. Full-compile timing includes process startup and captured
output, while helper timing uses `IO.monoNanosNow` inside one process. The
compiler sources and benchmark code are pinned by the commit containing this
report; the metadata baseline is the ordinary-merged tree before this audit.
