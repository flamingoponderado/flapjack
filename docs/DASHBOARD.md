# Port progress dashboard

`dashboard.html` is a self-contained HTML page that visualises how much of the
CakeML/HOL Pancake development has been ported to Lean. Open it in any browser;
it needs no build step or network.

Regenerate it from the repository root:

```sh
python3 scripts/build-dashboard.py            # writes ./dashboard.html
python3 scripts/build-dashboard.py --out /tmp/dashboard.html
```

It uses only the Python standard library and the same authoritative sources the
rest of the port's tooling uses, so the numbers stay consistent with CI:

- `docs/HOL-THEOREM-MAP.json` — the reviewed HOL↔Lean declaration map
  (checked by `scripts/check-hol-refs.py` and `scripts/check_hol_ref_export.py`).
- `.hol-index/` — the CakeML/HOL source index from `scripts/index-hol.py`
  (declaration kinds, per-script totals, and the theory dependency graph in
  `theory-deps.txt`, used for dependency ordering). The script refreshes a stale
  index automatically, like `scripts/next-hol-port.py`.
- a direct scan of the `@[hol ...]` tags in `Flapjack/` — the source-of-truth
  count of ported declarations and their Lean keyword (theorem/def/…).

## What the tabs show

- **Overview** — headline counts, with two extra
  sections: **Port scope completion**, which measures how much of the *in-scope*
  CakeML surface (see below) has a port, with the largest still-unported scripts
  listed; and **End-to-end correctness · AST → RISC-V**, which lays out the
  verified source-to-machine chain(s) for both front-ends. CakeML and Pancake
  share the same backend and RISC-V target encoder, so both reach RISC-V through
  `riscv_encoder_correct`; the chains differ at the front end — Pancake's
  `pan_to_target_compile_semantics` is ported, while CakeML's `compile_correct`
  (source → installed machine code) is shown as not yet ported.
  The CakeML `compile_correct` step is **expandable**: it lists the correctness
  theorems it composes on the HOL side — the front-end and type-soundness lemmas
  (all unported) plus the per-pass backend chain (`compile_correct'`: flat → clos
  → bvl → bvi → data → word → stack → lab → target), each badged ported/not
  ported. Of the 26 constituents, 18 are ported; the unported ones are the whole
  CakeML front-end (parse, infertype, compile) and four backend passes
  (`bvi_let`, `data_live`, `data_simp`, `data_to_word`).
- **Pipeline** — the curated major-compilation passes in order from the CakeML
  front-end through the shared backend to RISC-V, one row per `<pass>ProofScript.sml`,
  each with a coloured badge for whether that pass's *headline* semantic-preservation
  theorem has been ported (green = reviewed, grey = not ported). It shows the CakeML
  compiler only — its front-end (`parse`, `infertype`, `compile`, all not yet ported)
  then the shared backend passes (clos → bvl → bvi → data → word → stack → lab →
  target) — not the separate Pancake front-end. It is a per-pass heuristic, not a
  per-theorem review: a pass usually carries additional supporting theorems.
- The **status** colours come straight from the map: **reviewed** means a HOL
  correspondence was source-reviewed (`reviewed_*`); **pending classification**
  is Flapjack-only work awaiting a HOL original; **documented mismatch** is a
  known statement difference kept untagged.

## Reading the numbers

A ported `@[hol]` tag records a reviewed source comparison, *not* a proof of
HOL↔Lean equivalence; see `docs/SOUNDNESS.md`. The dependency order is the
original proof's theory-dependency depth, so it is the recommended port order,
not a claim about any single pull request. Whole-tree HOL counts on the Overview
are context only — most CakeML/HOL theories (examples, CNF, deflate, …) are
outside this Pancake compiler port and are not the denominator.

**Port scope** (used by the Overview "Port scope completion" section and the
Pipeline tab) is CakeML source under `pancake/`, `compiler/`, `semantics/`,
`basis/`, and `examples/l3-machine-code/`, excluding the candle translator and
characteristic-files trees. "Scripts ported" counts in-scope proof/definition
scripts that have at least one map entry — a clean same-unit figure. The
"source declarations" share uses the CakeML index on both sides, but those index
totals are best-effort and are *not* a rigorous port denominator.
