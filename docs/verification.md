# Verification

What the checks of this repository establish, and how to run them.

| Check | How |
| --- | --- |
| Every module builds with warnings treated as errors | `bash scripts/ci_build.sh` (`lake --wfail build`, then `scripts/check_clean_log.py`) |
| The registry of external inputs matches the Lean axioms, and the statement map and source inventory match the files | `python3 scripts/check_public_inputs.py` |
| The 69 axiom reports of `PublicVerification/Axioms.lean`: Theorem 1.1 uses only `propext`, `Classical.choice` and `Quot.sound`; the 22 proved results from the literature use only these three axioms; every other report lists only standard and registered axioms | `scripts/check_public_axioms.py`, run by `scripts/ci_build.sh` |
| No `sorry`, `admit` or `native_decide` in the production files | `scripts/check_public_inputs.py` |
| No reference to a local machine in any file | `python3 scripts/lint_public.py .` |
| The comparator accepts the solution of the Theorem 1.1 challenge, with the Lean kernel and the nanoda kernel | `scripts/build_comparator_tools.sh`, `scripts/run_comparators.sh` |

The continuous integration runs the first five checks on every push (`build.yml`) and the
comparator in a separate workflow (`comparator.yml`).

The inventory has 1537 Lean files: 1536 production modules and the axiom query
`PublicVerification/Axioms.lean`. The statement map covers the 17 numbered statements of the
paper.

No external result is assumed by Theorem 1.1. The 22 registered results that the proofs use are
proved in Lean with their statements unchanged; three of them use Lattice-Probability. The
registry keeps three further axioms that Theorem 1.1 does not use. Source references, where
identified, are recorded in `audit/trusted-inputs.json`.

The comparator pair `FiniteAvalanchesAudit/MainOrigin/` is captured with
`scripts/capture_main_origin.py`: emit the capture program with
`python3 scripts/capture_main_origin.py .lake/CaptureMainOrigin.lean`, run it with
`lake env lean .lake/CaptureMainOrigin.lean`, normalize the output with
`python3 scripts/capture_main_origin.py --normalize .lake/main-origin-capture`, and copy the six
files into `FiniteAvalanchesAudit/MainOrigin/semantic-data/`. The current capture has 4014
declarations, no retained axiom and the unchanged type of Theorem 1.1; the comparator permits
exactly `propext`, `Classical.choice` and `Quot.sound`.

The pairs for the earlier sources with 19 and 8 literature inputs passed the comparator workflow
in continuous integration. The release review and the comparator review in
`audit/release-eligibility.json` and `audit/comparator-review.json` are pending for the current
source, and the review-gated checks cannot pass until they are recorded.
