# Sandpile avalanches in two dimensions are finite

A Lean 4 formalization of Ahmed Bou-Rabee's paper *Sandpile avalanches in two dimensions are finite*.

[![CI](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml)
[![Comparator](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml)

All **16 numbered statements** have proved Lean declarations, relative to **26 explicitly listed external inputs** from the literature. The proof establishes almost-sure finite stabilization after one grain is added at the origin under the infinite-volume recurrent sandpile measure on the square lattice. It also bounds the avalanche-radius tail by a negative power of the logarithm.

The [main theorem](FiniteAvalanchesFrozen/MainOriginV3.lean) states the full result. The [paper correspondence](CORRESPONDENCE.md) identifies every numbered statement. The local-comparison and revealed-root statements share one declaration and one uniform constant.

## External inputs

The allowed axioms are `propext`, `Classical.choice`, `Quot.sound` and the 26 standard results in the [external-input registry](audit/trusted-inputs.json). Those results remain assumptions; they are not claimed as proved Lean theorems. The registry records their complete declarations, mathematical sources and the definitions used in their statements.

Two former external inputs, wired hitting probability equals voltage and recurrence implies hitting an arbitrary lattice site, now have proofs. Their reusable parts are in [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability). Work continues there on the remaining inputs.

## Verification

The release source passed independent review, a fresh warning-free build and the main-theorem comparator with Lean and NanoDa replay. These checks verify the proof relative to the 26 listed external inputs.

CI builds the production library with warnings treated as errors and checks all 4,737 requested axiom reports against the exact external-input registry. The two proved replacements and their providers and consumers must use only Lean's three logical axioms.

The comparator checks a Mathlib-only statement of the full main theorem against its library proof and replays the solution with Lean and NanoDa. Its single intentional challenge hole is outside the production library. Tool revisions, permitted axioms and sandbox protections are fixed; a missing comparison fails the check.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
bash scripts/ci_build.sh
```

Lean 4.32.0, Mathlib and Lattice-Probability are pinned. A fresh build compiles project sources and source dependencies; project proof objects are not restored from a CI cache.

## Layout

| Path | Contents |
| --- | --- |
| `FiniteAvalanches/` | Sandpile, spanning-tree, Wilson and electrical proofs |
| `FiniteAvalanchesFrozen/` | Exact source statements and proved exports |
| `FiniteAvalanchesProofs/` | Proof assemblies for the source statements |
| `FiniteAvalanchesAudit/` | Independent main-theorem comparator |
| `audit/` | Current statement map and explicit external inputs |
| `scripts/` | Build, axiom and comparator checks |

There are 841 production Lean files and 88,755 physical lines, excluding dependencies and comparator sources. The development used AI-assisted proof writing under human direction. Please cite the paper when using this work.
