#!/usr/bin/env bash
# A closure report is not a comparator. Only actual matching+Lean+NanoDa counts.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
mkdir -p .lake/comparator-logs
python3 -B scripts/prepare_public_comparators.py --check \
  2>&1 | tee .lake/comparator-logs/preflight.log
test "$(cat lean-toolchain)" = 'leanprover/lean4:v4.32.0'
test "$(id -u)" -ne 0
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to the reviewed freshly built tools directory}"
python3 -B scripts/check_comparator_tools.py "$COMPARATOR_TOOLS" \
  2>&1 | tee .lake/comparator-logs/tool-pins.log
# Refuse stale audit objects rather than delete or reuse them. The workflow
# restores dependency objects only and does not build the solution beforehand.
python3 -B - <<'PY'
from pathlib import Path
if any(p.is_file() for p in Path('.lake/build').glob('**/FiniteAvalanchesAudit/**/*')):
    raise SystemExit('Audit artifacts already exist; use a fresh checkout for comparator verification.')
PY
export COMPARATOR_REAL_LANDRUN="$COMPARATOR_TOOLS/bin/landrun"
export COMPARATOR_LANDRUN="$COMPARATOR_TOOLS/bin/comparator-landrun"
export COMPARATOR_LEAN4EXPORT="$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$COMPARATOR_TOOLS/nanoda/target/release/nanoda_bin"
comparator="$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator"
for tool in "$COMPARATOR_REAL_LANDRUN" "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA" "$comparator"; do
  test -x "$tool" || { echo "Missing executable: $tool" >&2; exit 1; }
done
# Require the upstream-prescribed AF_UNIX restriction, with no insecure fallback.
systemd-run --user --wait --pipe --property=RestrictAddressFamilies=~AF_UNIX -- /bin/true
config_parent=$(mktemp -d "${TMPDIR:-/tmp}/finite-avalanche-comparator.XXXXXXXX")
trap 'rm -rf "$config_parent"' EXIT
python3 -B scripts/prepare_public_comparators.py --output "$config_parent/configs"
probe="$config_parent/escape"
"$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec -- /bin/true
"$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec \
  -- /bin/sh -c 'printf escaped > "$1"' sh "$probe" || true
test ! -e "$probe" || { echo 'Sandbox allowed an outside write' >&2; exit 1; }
unset LEAN_PATH
# The dedicated Actions job has no project-object cache and never prebuilds audit
# solutions. Comparator itself builds Challenge/Solution inside its sandbox.
count=0
while IFS=$'\t' read -r source_config protected_config; do
  log=".lake/comparator-logs/$count.log"
  systemd-run --user --wait --pipe --working-directory="$root" \
    --property=RestrictAddressFamilies=~AF_UNIX \
    -E "PATH=$PATH" -E "HOME=$HOME" \
    -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
    -E "COMPARATOR_REAL_LANDRUN=$COMPARATOR_REAL_LANDRUN" \
    -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
    -E "COMPARATOR_NANODA=$COMPARATOR_NANODA" \
    -- lake env "$comparator" "$protected_config" 2>&1 | tee "$log"
  grep -Fxq 'Your solution is okay!' "$log"
  grep -Fxq 'Nanoda kernel accepts the solution' "$log"
  count=$((count+1))
  printf '%s: comparator/Lean/NanoDa PASS\n' "$source_config"
done < "$config_parent/configs/pairs.tsv"
test "$count" -eq 1
