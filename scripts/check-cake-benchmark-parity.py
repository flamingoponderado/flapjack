#!/usr/bin/env python3
"""Compare CakeML benchmark assembly against the pinned compiler's captures."""
import argparse
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts/hol-probes/cake_benchmark_pinned.json"
spec = importlib.util.spec_from_file_location("cake_cli_parity", ROOT / "scripts/check-cake-cli-parity.py")
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

BENCHMARKS = {
    "cakeml_benchmarks": ["reverse", "nqueens", "qsort", "bst_contain", "queue", "fib", "qsortimp",
                           "btree", "sptree_contain", "foldl", "array_contain"],
    "mlton_benchmarks": ["flat-array", "life", "vector-concat", "vector-rev", "fib", "imp-for", "tak",
                          "logic", "tailfib", "even-odd", "merge", "mpuz", "ratio-regions", "knuth-bendix",
                          "smith-normal-form", "pidigits"],
}


# Standalone sources shipped with CakeML outside the main benchmark corpus.
EXTRA_SOURCES = {
    "bootstrap/x64/test-hello": "compiler/bootstrap/compilation/x64/64/test-hello.cml",
    "bootstrap/x64/hello": "compiler/bootstrap/compilation/x64/hello.cml",
    "bootstrap/arm8/hello": "compiler/bootstrap/compilation/arm8/hello.cml",
    "cakeml_benchmarks/dummy_contain": "compiler/benchmarks/cakeml_benchmarks/cakeml/dummy_contain.cml",
}


def sources():
    for group, names in BENCHMARKS.items():
        for name in names:
            yield f"{group}/{name}", Path("compiler/benchmarks") / group / "cakeml" / f"{name}.cml"
    for name, path in EXTRA_SOURCES.items():
        yield name, Path(path)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def result(executable, source):
    process = subprocess.run([str(executable), "--target=riscv"], input=source,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    return {"exit_code": process.returncode,
            "stdout_bytes": len(process.stdout), "stdout_sha256": digest(process.stdout),
            "stderr_bytes": len(process.stderr), "stderr_sha256": digest(process.stderr)}


def check_sources():
    cakeml = ROOT / "cakeml"
    revision = subprocess.check_output(["git", "-C", str(cakeml), "rev-parse", "HEAD"], text=True).strip()
    if revision != parity.PINNED_REV:
        raise SystemExit(f"unexpected CakeML source revision: {revision}")
    paths = [str(path) for _, path in sources()]
    if subprocess.run(["git", "-C", str(cakeml), "diff", "--quiet", "HEAD", "--", *paths]).returncode != 0:
        raise SystemExit("benchmark sources differ from the pinned CakeML revision")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record-reference", type=Path, help="regenerate captures with the pinned compiler")
    parser.add_argument("--check-reference", type=Path, help="also compare the pinned compiler with captures")
    parser.add_argument("--cake", type=Path, default=ROOT / ".lake/build/bin/cake")
    args = parser.parse_args()
    check_sources()
    if args.record_reference:
        parity.check_pinned_reference(args.record_reference)
        rows = {}
        for name, path in sources():
            source = (ROOT / "cakeml" / path).read_bytes()
            output = result(args.record_reference, source)
            if output["exit_code"] != 0 or output["stdout_bytes"] == 0 or output["stderr_bytes"] != 0:
                raise SystemExit(f"{name}: pinned compiler did not successfully emit assembly: {output}")
            rows[name] = {"source_sha256": digest(source), **output}
        FIXTURE.write_text(json.dumps({"cakeml_revision": parity.PINNED_REV,
                                       "hol_revision": parity.HOL_REV, "cases": rows}, indent=2) + "\n")
    expected = json.loads(FIXTURE.read_text())
    if (expected["cakeml_revision"], expected["hol_revision"]) != (parity.PINNED_REV, parity.HOL_REV):
        raise SystemExit("unexpected reference provenance")
    if set(expected["cases"]) != {name for name, _ in sources()}:
        raise SystemExit("reference case list has changed")
    if args.check_reference:
        parity.check_pinned_reference(args.check_reference)
    for name, path in sources():
        source = (ROOT / "cakeml" / path).read_bytes()
        want = expected["cases"][name]
        if digest(source) != want["source_sha256"]:
            raise SystemExit(f"{name}: benchmark source does not match the capture")
        expected_output = {key: value for key, value in want.items() if key != "source_sha256"}
        if args.check_reference and result(args.check_reference, source) != expected_output:
            raise SystemExit(f"{name}: pinned compiler no longer matches its capture")
        actual = result(args.cake, source)
        if actual != expected_output:
            raise SystemExit(f"{name}: output mismatch\nexpected {expected_output}\nactual   {actual}")
        print(f"{name}: complete output matches pinned CakeML", flush=True)


if __name__ == "__main__":
    main()
