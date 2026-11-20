# Verification

What the checks of this repository establish, and how to run them.

| Check | How |
| --- | --- |
| Every module builds with warnings treated as errors | `bash scripts/ci_build.sh` (`lake --wfail build`, then `scripts/check_clean_log.py`) |
| The registry of external inputs matches the Lean axioms, and the statement map and source inventory match the files | `python3 scripts/check_public_inputs.py` |
| The 69 axiom reports of `PublicVerification/Axioms.lean`: Theorem 1.1 uses exactly the 8 registered axioms of its proof and `propext`, `Classical.choice`, `Quot.sound`; the 14 proved results use only the three standard axioms; every other report lists only standard and registered axioms | `scripts/check_public_axioms.py`, run by `scripts/ci_build.sh` |
| No `sorry`, `admit` or `native_decide` in the production files | `scripts/check_public_inputs.py` |
| No reference to a local machine in any file | `python3 scripts/lint_public.py .` |
| The comparator accepts the solution of the Theorem 1.1 challenge, with the Lean kernel and the nanoda kernel | `scripts/build_comparator_tools.sh`, `scripts/run_comparators.sh` |

The continuous integration runs the first five checks on every push (`build.yml`) and the
comparator in a separate workflow (`comparator.yml`).

The inventory has 1440 Lean files: 1439 production modules and the axiom query
`PublicVerification/Axioms.lean`. The statement map covers the 17 numbered statements of the
paper.

Eight external results used by Theorem 1.1 remain axioms. Fourteen registered results are proved
in Lean with their statements unchanged; three of them use Lattice-Probability. Source references,
where identified, are recorded in `audit/trusted-inputs.json`.

The comparator pair `FiniteAvalanchesAudit/MainOrigin/` is captured with
`scripts/capture_main_origin.py`: emit the capture program with
`python3 scripts/capture_main_origin.py .lake/CaptureMainOrigin.lean`, run it with
`lake env lean .lake/CaptureMainOrigin.lean`, normalize the output with
`python3 scripts/capture_main_origin.py --normalize .lake/main-origin-capture`, and copy the six
files into `FiniteAvalanchesAudit/MainOrigin/semantic-data/`. The current capture has 1976
declarations, the 8 retained axioms and the unchanged type of Theorem 1.1.

The pair for the earlier 19-input source passed the comparator workflow in continuous
integration. The independent release review and comparator review of the current source and pair
are recorded in `audit/release-eligibility.json` and `audit/comparator-review.json`, bound to the
current source inventory; the comparator run of the current pair is made by the workflow.
