# Verification

What the checks of this repository establish, and how to run them.

| Check | How |
| --- | --- |
| Every module builds with warnings treated as errors | `bash scripts/ci_build.sh` (`lake --wfail build`, then `scripts/check_clean_log.py`) |
| The registry of external inputs matches the Lean axioms, and the statement map and source inventory match the files | `python3 scripts/check_public_inputs.py` |
| The 69 axiom reports of `PublicVerification/Axioms.lean`: Theorem 1.1 uses exactly the 12 registered axioms of its proof and `propext`, `Classical.choice`, `Quot.sound`; every other report lists only standard and registered axioms | `scripts/check_public_axioms.py`, run by `scripts/ci_build.sh` |
| No `sorry`, `admit` or `native_decide` in the production files | `scripts/check_public_inputs.py` |
| No reference to a local machine in any file | `python3 scripts/lint_public.py .` |
| The comparator accepts the solution of the Theorem 1.1 challenge, with the Lean kernel and the nanoda kernel | `scripts/build_comparator_tools.sh`, `scripts/run_comparators.sh` |

The continuous integration runs the first five checks on every push (`build.yml`) and the
comparator in a separate workflow (`comparator.yml`).

The inventory has 1162 Lean files: 1161 production modules and the axiom query
`PublicVerification/Axioms.lean`. The statement map covers the 17 numbered statements of the
paper.

Twelve external results used by Theorem 1.1 remain axioms. Ten additional results are proved
in Lean. Source references are recorded in `audit/trusted-inputs.json`. The release and comparator reviews bind the earlier source inventory and must be
renewed for the current source before the corresponding review-gated checks can pass.

The source and axiom check scripts currently enforce the earlier counts of 20
assumptions, 17 used by the main theorem, and five proved results. They need to
be updated to the counts in the current registry before the static check can pass.
