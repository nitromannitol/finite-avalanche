# Sandpile avalanches in two dimensions are finite

A Lean 4 formalization of Ahmed Bou-Rabee's paper *Sandpile avalanches in two dimensions are finite*.

[![Current source CI](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml?query=branch%3Amain)
[![Current Main comparator](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml?query=branch%3Amain)

The [Main theorem](FiniteAvalanchesCurrent/RegisteredPast/Main.lean) concerns **all integer sandpile fields**. It states almost-sure legal stabilization after adding one grain at the origin and a logarithmic radius-tail bound with one exponent and constant before every nonnegative real threshold.

Main is conditional on **exactly 22 named standard external assumptions**. The [registry](audit/trusted-inputs.json) lists **25 registered assumptions** and identifies Main's 22. These inputs remain assumptions; their proofs are deferred. The permitted logical axioms are `propext`, `Classical.choice` and `Quot.sound`. Pólya site hitting, wired first-hit voltage and Kirchhoff signed tree path/current have ordinary Lean proofs, checked separately from the assumptions. The full BSST assumption remains registered and unused by Main.

The formalization targets the final round61 manuscript: revision `2ff7e75e9b6d626dc6c6243fa3d25fd179b34cf2`, parent `85a84fa1519eac9d9eaa0242cd7539d736e7090b`, and `main.tex` SHA256 `d2a875c154db9ff913ec6b25cf38e8da134ca977f6a24fd9c036cd8873b1082a`. The [statement map](audit/current-statements.json) records **17 numbered statements and 16 proof blocks**. The new means lemma joins all-original-edge absolute conjugacy, signed boundary means, and total mean equal to the grounded Green diagonal and original energy. The arc and split estimates use literal indicator expectations. Local comparison and revealed roots retain one joint declaration and shared epsilon. Manuscript source is not included.

Independent review of the 17 numbered statements and their definitions and proof routes has passed. The isolated public-source build passes with zero warnings, all **69 direct axiom reports** pass, and the current Main comparator passes actual matching, Lean and NanoDa kernel replay, and both full environment queries. The local build extended authenticated objects from this public source tree; hosted workflows compile fresh project objects. **Hosted CI and comparator are pending for this public update.** Badges display actual hosted outcomes; earlier runs do not verify this update. [Verification scope](docs/verification.md) describes the gates. The [electrical voltage note](docs/electrical-voltage.md) describes the distinct-pole domain.

## Build

Lean 4.32.0, Mathlib and Lattice-Probability are pinned. In a fresh checkout with [elan](https://github.com/leanprover/elan):

```bash
lake exe cache get
bash scripts/ci_build.sh
```

The build compiles all production modules with warnings treated as errors, generates fresh direct axiom reports, and checks Main's exact 22-input closure. CI restores dependency objects only. Source review eligibility must pass before verification can pass.

The comparator uses the [pinned tools](audit/comparator-tool-pins.json). Its Mathlib-only challenge has one intentional theorem hole outside production defaults. The solution must prove the complete Main statement; actual matching, Lean and NanoDa kernel replays, and complete environment queries are required.

## Source layout

| Path | Contents |
| --- | --- |
| `FiniteAvalanches/` | Sandpile, spanning-tree, Wilson and electrical proofs |
| `FiniteAvalanchesCurrent/` | Source-facing statements and exact applications |
| `CurrentRegisteredPast/` | Main and reduction assemblies |
| `CurrentSource/` | Electrical and whole-integer constructions |
| `PublicVerification/` | Direct axiom requests |
| `audit/` | Source inventory, statement map and external assumptions |
| `scripts/` | Build, axiom, privacy and comparator checks |

The inventory contains **894 production and verification Lean files** (94593 physical lines), with **893 production default targets** excluding the direct axiom query. Pinned dependencies and comparator sources are excluded from these counts. Development used AI-assisted proof writing under human direction. Please cite the paper when using this work.
