#!/usr/bin/env bash
# Materialize the local .olean files of a Lake target from the Lake artifact
# cache, so tools that only read LEAN_PATH (`lake env lean`, plain `lean`, some
# editors) can import Flapjack modules.
#
# With LAKE_ARTIFACT_CACHE=true, Lake 5 records cached outputs in synthetic
# `.trace` files and passes `lean --setup <json>` pointing at the cache
# (`$LAKE_CACHE_DIR/artifacts/<hash>.olean`). `lake build` and `lake lean` work,
# but `.lake/build/lib/lean/**/*.olean` is not written for reused modules, so
# LEAN_PATH-only compilation fails with "object file ... does not exist".
#
# LAKE_RESTORE_ARTIFACTS=true makes Lake itself restore those outputs into
# `.lake/build` (a hardlink to the content-addressed cache entry selected by the
# module's input hash). This is not a cross-worktree copy: Lake re-checks the
# trace against the current sources and rebuilds anything whose inputs changed.
# Nothing is deleted.
#
# Usage: scripts/lake-restore-oleans.sh [TARGET ...]   (default: Flapjack)
set -euo pipefail
cd "$(dirname "$0")/.."

targets=("$@")
if [ ${#targets[@]} -eq 0 ]; then
  targets=(Flapjack)
fi

LAKE_RESTORE_ARTIFACTS=true lake build "${targets[@]}"

status=0
for target in "${targets[@]}"; do
  case "$target" in
    Flapjack.*)
      olean=".lake/build/lib/lean/$(echo "$target" | tr . /).olean"
      if [ -e "$olean" ]; then
        echo "ok: $olean"
      else
        echo "missing OLean after restore: $olean" >&2
        status=1
      fi
      ;;
  esac
done

echo "$(find .lake/build/lib/lean/Flapjack -name '*.olean' | wc -l) Flapjack OLean files present"
exit "$status"
