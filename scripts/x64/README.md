# x86-64 parity fixtures

Each `<case>.pnk` is a Pancake source.  `<case>.cake.S` is the exact output of
the original CakeML compiler:

```sh
cakeml/developers/bin/cake --pancake --target=x64 < <case>.pnk
```

`<case>.cake.hex` is the lowercase hex of the `.byte` payload in `.cake.S`.
`Flapjack/Test/X64Parity.lean` checks both the whole assembly text and this
payload against `flapjack-compile --target=x64`, so `lake test` needs no CakeML
binary.  With a CakeML build available, re-check or regenerate the goldens:

```sh
scripts/x64/check-parity.py --cake /path/to/cake
scripts/x64/check-parity.py --cake /path/to/cake --regenerate
```

`scripts/x64/fuzz.py` generates random Pancake programs and compares the full
assembly output of the two compilers.  Programs the original compiler rejects
(`### ERROR: ...`) are counted as rejections; any other nonzero oracle exit is a
failure, and the run fails unless at least `--min-compared` (default half of
`--count`) programs were actually compared.

See `docs/X64.md` for the backend status and `docs/PARITY-TESTING.md` for the
evidence rule.
