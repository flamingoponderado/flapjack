#!/usr/bin/env bash
set -euo pipefail

# The checkout is kept outside the source submodules because HOL builds write
# generated files. Supply a built HOL checkout at the revision pinned here.
repo=$(cd "$(dirname "$0")/.." && pwd)
cake_dir=${CAKEML_BUILD_DIR:-/var/tmp/flapjack-cakeml-oracle}
hol_dir=${HOL4:-/home/zksecurity/HOL}
cake_rev=$(git -C "$repo" rev-parse HEAD:cakeml)
hol_rev=$(git -C "$repo" rev-parse HEAD:HOL)

if [[ $(git -C "$cake_dir" rev-parse HEAD) != "$cake_rev" ]]; then
  echo "CakeML build checkout does not match pinned revision $cake_rev" >&2
  exit 1
fi
if [[ $(git -C "$hol_dir" rev-parse HEAD) != "$hol_rev" ]]; then
  echo "HOL build checkout does not match pinned revision $hol_rev" >&2
  exit 1
fi
if ! git -C "$cake_dir" diff --quiet HEAD -- || ! git -C "$hol_dir" diff --quiet HEAD --; then
  echo "CakeML and HOL build checkouts must have no tracked modifications" >&2
  exit 1
fi
if [[ ! -x "$hol_dir/bin/Holmake" ]]; then
  echo "Built HOL is missing $hol_dir/bin/Holmake" >&2
  exit 1
fi

build_dir="$cake_dir/compiler/bootstrap/compilation/x64/64"
(cd "$build_dir" && CAKEMLDIR="$cake_dir" "$hol_dir/bin/Holmake" -j "${CAKE_BUILD_JOBS:-2}" cake)
if [[ ! -x "$build_dir/cake" ]]; then
  echo "CakeML bootstrap did not produce $build_dir/cake" >&2
  exit 1
fi
version=$("$build_dir/cake" --version)
if ! grep -Fq "CakeML: $cake_rev" <<<"$version" || ! grep -Fq "HOL4:   $hol_rev" <<<"$version"; then
  echo "Built cake reports revisions different from the pinned source:" >&2
  printf '%s\n' "$version" >&2
  exit 1
fi
printf '%s\n' "$version"
printf 'Pinned CakeML executable: %s\n' "$build_dir/cake"
