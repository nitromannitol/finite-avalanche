# Verification

What the checks of this repository establish, and how to run them.

| Check | How |
| --- | --- |
| Every module builds with warnings treated as errors | `bash scripts/ci_build.sh` (`lake --wfail build`, then `scripts/check_clean_log.py`) |
| The registry of external inputs matches the Lean axioms, and the statement map and source inventory match the files | `python3 scripts/check_public_inputs.py` |
| The 69 axiom reports of `PublicVerification/Axioms.lean`: Theorem 1.1 uses exactly the 22 registered axioms of its proof and `propext`, `Classical.choice`, `Quot.sound`; every other report lists only standard and registered axioms | `scripts/check_public_axioms.py`, run by `scripts/ci_build.sh` |
| No `sorry`, `admit` or `native_decide` in the production files | `scripts/check_public_inputs.py` |
| No reference to a local machine in any file | `python3 scripts/lint_public.py .` |
| The comparator accepts the solution of the Theorem 1.1 challenge, with the Lean kernel and the nanoda kernel | `scripts/build_comparator_tools.sh`, `scripts/run_comparators.sh` |

The continuous integration runs the first five checks on every push (`build.yml`) and the
comparator in a separate workflow (`comparator.yml`).

The inventory has 894 Lean files: 893 production modules and the axiom query
`PublicVerification/Axioms.lean`. The statement map covers the 17 numbered statements of the
paper.

The 22 external results are axioms. Checking their Lean statements against the cited sources is
a reading, recorded with page references in `audit/trusted-inputs.json`; the checks above do not
prove them.
