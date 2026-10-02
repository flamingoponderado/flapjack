#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/../.." && pwd)
hol_dir=${HOL4:-"$repo_dir/HOL"}
mode=${1:---update}
if [[ "$mode" != --check && "$mode" != --update ]] || [[ $# -gt 1 ]]; then
  echo "usage: $0 [--check|--update]" >&2
  exit 2
fi

# The loaded original theories must be built at this checkout's HOL pin.
expected=$(git -C "$repo_dir" rev-parse HEAD:HOL)
actual=$(git -C "$hol_dir" rev-parse HEAD)
if [[ "$expected" != "$actual" ]]; then
  echo "HOL revision mismatch: expected $expected, found $actual" >&2
  exit 2
fi
if [[ ! -x "$hol_dir/bin/hol" ]]; then
  echo "Build the pinned HOL and its original riscv_step theory first." >&2
  exit 2
fi

export_dir=$(mktemp -d)
trap 'rm -rf "$export_dir"' EXIT
(cd "$export_dir" && "$hol_dir/bin/hol" run "$repo_dir/scripts/l3/export_riscv_defs.sml") \
  > "$export_dir/export.log"
artifact="$repo_dir/scripts/l3/riscv_defs.sexp.gz"
if [[ "$mode" == --check ]]; then
  gzip -dc "$artifact" > "$export_dir/committed.sexp"
  cmp "$export_dir/defs.sexp" "$export_dir/committed.sexp"
else
  gzip -9 -n < "$export_dir/defs.sexp" > "$export_dir/defs.sexp.gz"
  cp "$export_dir/defs.sexp.gz" "$artifact"
fi
echo "Original pinned HOL export matches: $(wc -l < "$export_dir/defs.sexp") complete definitions ($expected)"
