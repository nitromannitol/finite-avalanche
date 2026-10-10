#!/usr/bin/env bash
# No project-object cache is restored: all project warning checks execute afresh.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
unset LEAN_PATH
mkdir -p .lake/verification-logs
test "$(cat lean-toolchain)" = 'leanprover/lean4:v4.32.0'
# The proposed Lake patch removes this package-wide suppression. Fail rather
# than describe a suppressed diagnostic as a warning-free build.
if grep -Fq 'warn.classDefReducibility' lakefile.lean; then
  echo 'Remove the classDefReducibility suppression before this verification run.' >&2
  exit 1
fi
lake env lean --version | tee .lake/verification-logs/toolchain.log
python3 -B scripts/check_public_inputs.py | tee .lake/verification-logs/trusted-inputs.log
lake --no-ansi --wfail build 2>&1 | tee .lake/verification-logs/build.log
python3 -B scripts/check_clean_log.py .lake/verification-logs/build.log
# A direct invocation guarantees fresh reports even when the audit target is cached.
lake env lean \
  -DwarningAsError=true \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true \
  -Dlinter.deprecated=true \
  FiniteAvalanches/Meta/AxiomsAudit.lean \
  2>&1 | tee .lake/verification-logs/axioms.log
python3 -B scripts/check_clean_log.py .lake/verification-logs/axioms.log
python3 -B scripts/check_public_axioms.py .lake/verification-logs/axioms.log \
  | tee .lake/verification-logs/axiom-boundary.log
