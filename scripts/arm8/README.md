# ARMv8 parity fixtures

Each `<case>.pnk` is a Pancake source. `<case>.cake.S` is the exact output of the
original CakeML compiler:

```sh
cakeml/developers/bin/cake --pancake --target=arm8 < <case>.pnk
```

`<case>.cake.hex` is the lowercase hex of the `.byte` payload in `.cake.S`.
`Flapjack/Test/Arm8Parity.lean` checks both the whole assembly text and this
payload against `flapjack-compile --target=arm8`, so `lake test` needs no CakeML
binary. With a CakeML build available, re-check or regenerate the goldens:

```sh
scripts/arm8/check-parity.py --cake /path/to/cake
scripts/arm8/check-parity.py --cake /path/to/cake --regenerate
```

See `docs/ARM8.md` for the backend status and `docs/PARITY-TESTING.md` for the
evidence rule.
