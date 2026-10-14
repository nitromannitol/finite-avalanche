#!/usr/bin/env bash
# Fresh project build and actual direct axiom reports; no project-object cache.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
unset LEAN_PATH
mkdir -p .lake/verification-logs
test "$(cat lean-toolchain)" = 'leanprover/lean4:v4.32.0'
if grep -Eq 'maxHeartbeats|warn\.classDefReducibility' lakefile.lean; then
  echo 'Unsupported resource or diagnostic override in Lakefile.' >&2
  exit 1
fi
python3 -B scripts/lint_public.py . | tee .lake/verification-logs/privacy.log
lake env lean --version | tee .lake/verification-logs/toolchain.log
python3 -B scripts/check_public_inputs.py | tee .lake/verification-logs/trusted-inputs.log
lake --no-ansi --wfail build 2>&1 | tee .lake/verification-logs/build.log
python3 -B scripts/check_clean_log.py .lake/verification-logs/build.log
lake env lean \
  -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true \
  -Dlinter.deprecated=true PublicVerification/Axioms.lean \
  2>&1 | tee .lake/verification-logs/axioms.log
python3 -B scripts/check_clean_log.py .lake/verification-logs/axioms.log
python3 -B scripts/check_public_axioms.py .lake/verification-logs/axioms.log \
  | tee .lake/verification-logs/axiom-boundary.log
