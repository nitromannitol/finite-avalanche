# Sandpile avalanches in two dimensions are finite

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*Sandpile avalanches in two dimensions are finite*](https://arxiv.org/abs/2610.13940),
> arXiv:2610.13940.

The formalized text is the arXiv v2 source (`main.tex`, SHA-256
`d2a875c154db9ff913ec6b25cf38e8da134ca977f6a24fd9c036cd8873b1082a`). All 17 numbered
statements of the paper are stated and proved in Lean, the main theorem among them. The proofs
use 22 standard results from the literature, which enter as named Lean axioms (see
[Standing assumptions and scope](#standing-assumptions-and-scope)).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and the
shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`).

[![CI](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/finite-avalanche/actions/workflows/comparator.yml)

## What is proved

In the abelian sandpile on `ℤ²`, a site with at least four grains topples by sending one grain to
each neighbour. Let `μ` be the stationary law of the sandpile on `ℤ²`, the limit of the
stationary laws on the boxes `[-N, N]²` constructed by Athreya and Járai. Theorem 1.1 of the
paper answers their question in two dimensions: adding one grain at the origin causes only
finitely many topplings, almost surely, and the radius `ρ` of the avalanche has a logarithmic
tail.

**Theorem 1.1** ([`FiniteAvalanchesCurrent/RegisteredPast/Main.lean`](FiniteAvalanchesCurrent/RegisteredPast/Main.lean)).
For `μ`-almost every sandpile `η`, the sandpile `η + δ₀` stabilizes, and there are universal
constants `a > 0` and `C < ∞` such that `μ(ρ > M) ≤ C (log(M + 2))^(-a)` for every `M ≥ 0`:

```lean
theorem FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a)
```

The theorem has no hypotheses. `FullInteger.sourceLaw` is the stationary law, a probability
measure on all integer fields `ℤ² → ℤ`; `RawFull.Stabilizes η (oneGrain 0) w` says that `w` is
a finite legal toppling sequence after which `η + δ₀` is stable; and the radius is the largest
`ℓ∞` distance from the origin of a site that topples, and `∞` when `η + δ₀` does not stabilize.

The other 16 numbered statements are the steps of the proof:

| Paper | Statement | Lean declaration |
| --- | --- | --- |
| Theorem 1.1 | finite avalanches and the logarithmic radius tail | `FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin` |
| Lemma 2.1 | burning with held vertices and the pasts in the uniform spanning tree | `FiniteAvalanchesCurrent.HeldBurning.held_burning` |
| Lemma 2.2 | monotonicity of the two-root-set forest laws `ν_{A,Γ}` | `FiniteAvalanches.Paper.CurrentSource.global_monotonicity` |
| Proposition 3.1 | reduction of the avalanche radius to `E[𝓛_N⁻¹]` | `FiniteAvalanches.Paper.RegisteredPast.FullInteger.reciprocal_reduction_limsup` |
| Proposition 3.2 | the logarithmic bound on `E[𝓛(K)⁻¹]` | `FiniteAvalanches.Paper.CurrentSource.forest_reciprocal_cofinite` |
| Lemma 3.3 | the conditional law of `𝓛_N` given the minimal subtree | `FiniteAvalanches.Paper.Current.finite_conditional_extended_contact_law` |
| Lemma 4.1 | the vertices that topple in a wave | `FiniteAvalanchesCurrent.Punctured.inverse_waves` |
| Lemma 4.2 | the outflow count of waves | `FiniteAvalanchesCurrent.Punctured.outflow` |
| Lemma 4.3 | the tail of the past of a vertex | `FiniteAvalanches.Paper.Revision4498.past_outside_origin_box_bound` |
| Proposition 5.1 | the lower bound at one scale | `FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed` |
| Proposition 5.2 | the mean and variance of `𝓛_{H₀}` in the reference network | `FiniteAvalanches.Electrical.Source.Reference.reference_moment_current` |
| Lemma 6.1 | the needle path | `FiniteAvalanchesFrozen.NeedlePathV5.needle_path` |
| Lemma 6.2 | the bound with revealed roots | `FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed` |
| Lemma 7.1 | conjugate Green differences and the means of the boundary edges | `FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means` |
| Lemma 7.2 | the pair-contact formula for `E[I_i I_j]` | `FiniteAvalanches.Electrical.Source.pair_contact_current` |
| Lemma 7.3 | the variance bound along the boundary arc | `FiniteAvalanches.Electrical.CurrentSourceRoots.arc_variance_expectations` |
| Lemma 7.4 | the split estimate for the grounded Green function | `FiniteAvalanches.Electrical.CurrentSourceRoots.split_estimate_expectations` |

Proposition 5.1 and Lemma 6.2 are proved as one declaration, which shares the constant `ε`
between them, as the paper does. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) links each declaration
and records how the Lean statements read the paper.

## Standing assumptions and scope

1. **Results from the literature.** Twenty-two standard results enter as named Lean axioms in
   [`FiniteAvalanches/External/`](FiniteAvalanches/External/), each with its source in the
   docstring. The axiom report of Theorem 1.1 consists of exactly these 22 axioms and
   `propext`, `Classical.choice` and `Quot.sound`. The registry
   [`audit/trusted-inputs.json`](audit/trusted-inputs.json) records, for each, its exact Lean
   statement and hash and its sources with page references.

   *Uniform spanning trees, sandpiles and random walk (10).*

   | Result | Lean axiom |
   | --- | --- |
   | Existence of the infinite-volume sandpile law on `ℤ²` (Athreya–Járai 2004, with the 2006 correction; Járai–Werning 2014) | `SandpileLimit.exists_infiniteVolumeLaw` |
   | The all-minors matrix-tree theorem (Chaiken 1982) | `allMinors_matrixTree` |
   | Weak convergence of the wired uniform spanning trees of the boxes (Pemantle; Häggström; BLPS; Lyons–Peres §10.1; Járai 2012) | `square_lattice_wired_ust_weak_limit` |
   | The wired uniform spanning tree of `ℤ²` is one tree with one end (BLPS Theorem 12.4; Lyons–Peres Theorems 10.30, 10.36, 10.41) | `square_lattice_wired_ust_one_tree_one_end` |
   | Planar duality of the uniform spanning tree (BLPS Theorem 12.2; Lyons–Peres §10.3) | `square_lattice_ust_dual_law` |
   | Wilson's algorithm with two root sets (Lyons–Peres Theorem 4.1 and §4.2) | `wilson_two_color_law_existsUnique` |
   | Domination of nested projection determinantal processes (Lyons 2003, Theorem 6.2) | `lyons_nestedProjectionDomination` |
   | The tail of the tree path between adjacent sites (Barlow–Masson 2011, Lemma 2.6) | `BarlowMasson2011.adjacent_ust_path_euclidean_tail` |
   | The Beurling estimate for simple random walk on `ℤ²` (Lawler–Limic 2004, Theorem 1) | `lawler_limic_beurling_srw_Z2` |
   | Pairing groves and response-matrix minors (Kenyon–Wilson 2009, Theorems 8.1 and B.3) | `kenyonWilson_pairingGroves_resistanceMinor` |

   *Topology of finite plane graphs (12)*, from Mohar–Thomassen, *Graphs on Surfaces*, Diestel,
   *Graph Theory*, Thomassen (1992) and Hatcher, *Algebraic Topology*: the impossibility of
   alternating crosscuts of a disk (`disk_alternation_impossible`), the face star of a vertex
   (`plane_vertex_face_star`), the faces of a two-pole plane network
   (`finite_plane_two_pole_topology`), extension and straightening of plane arcs
   (`parametrized_plane_arc_straightening`), redrawing a path of the outer face on the boundary of
   a disk (`outer_face_simple_path_disk_redrawing`), the geometric dual
   (`finite_plane_geometric_dual`), bonds as dual cycles (`finite_plane_dual_bond_cycle`),
   connectedness of the dual (`finite_plane_dual_connected`), complementary spanning trees
   (`finite_plane_tree_complement`), the faces on both sides of an edge
   (`plane_edge_chart_incidence`), and transport of faces under inversion of the punctured plane
   (`plane_punctured_face_transport`, `plane_punctured_chart_face_transport`).

   The registry contains three further standard results that Theorem 1.1 does not use: Wilson's
   algorithm on a finite network, ray-seeded Wilson sampling on `ℤ²` (van Engelenburg–Hutchcroft)
   and the square tiling of Brooks, Smith, Stone and Tutte.
2. **The model.** Sandpiles are integer fields on `ℤ²`; the stationary law is a probability
   measure on all of `ℤ² → ℤ`, and Theorem 1.1 quantifies over every integer field, not only the
   stable ones. Toppling sequences are finite lists of legal topplings.
3. **Quantifiers.** The constants `a` and `C` of Theorem 1.1 are chosen once, before every real
   threshold `M ≥ 0`, as printed. Proposition 5.1 and Lemma 6.2 share one constant `ε`.
4. **Electrical networks.** Networks keep every copy of a parallel edge, and energies sum over
   these copies. The voltage between two terminal sets is defined when the terminals are distinct;
   [`docs/electrical-voltage.md`](docs/electrical-voltage.md) describes the domain.
5. **Not formalized.** The paper's overview mentions a bound on the radius of avalanches in a
   finite box, which follows from Theorem 1.1; it is not a numbered statement and is not
   formalized separately. The figures and the survey of related work are not formalized.

## Guarantees

- **No `sorry`.** The library has none. The comparator challenge
  [`FiniteAvalanchesAudit/MainOrigin/Challenge.lean`](FiniteAvalanchesAudit/MainOrigin/Challenge.lean)
  contains one intentional statement-level `sorry`, which the solution proves.
- **Exact axiom boundary.** [`PublicVerification/Axioms.lean`](PublicVerification/Axioms.lean)
  prints 69 axiom reports, and [`scripts/check_public_axioms.py`](scripts/check_public_axioms.py)
  checks each of them: Theorem 1.1 uses exactly the 22 axioms above and the three standard
  axioms, and every other report lists only standard and registered axioms.
- **Warning-free build.** The continuous-integration build compiles every module with warnings
  treated as errors.
- **Independent check of the statement.** The challenge in
  [`FiniteAvalanchesAudit/MainOrigin/`](FiniteAvalanchesAudit/MainOrigin/) imports mathlib alone
  and rebuilds Theorem 1.1, with every definition it uses, from recorded kernel data.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the solution
  proves exactly this statement with only the three standard axioms and the 22 registered ones,
  through the Lean kernel and the independent nanoda kernel.
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability
  `8557b91360e23d51d779a05d8313974b403658b2`, recorded in [`lake-manifest.json`](lake-manifest.json).
- **Pinned statements and inputs.** [`audit/current-statements.json`](audit/current-statements.json)
  records, for each numbered statement, the line range and SHA-256 of its source in the paper and
  the hash of its Lean declaration; [`audit/source-inventory.json`](audit/source-inventory.json)
  records the hash of every production file.

[`docs/verification.md`](docs/verification.md) describes the checks in more detail.

## Size

About 94,500 lines of Lean in 894 files, of which about 81,700 lines are code once comments and
blank lines are removed, on top of mathlib and Lattice-Probability. The comparator surface under
`FiniteAvalanchesAudit/` and the axiom query `PublicVerification/` are not counted.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in
[`lean-toolchain`](lean-toolchain). From a fresh clone:

```bash
lake exe cache get        # prebuilt mathlib
bash scripts/ci_build.sh  # the build and the axiom checks run by the continuous integration
```

`scripts/ci_build.sh` checks the registry of external inputs
(`scripts/check_public_inputs.py`), builds every module with warnings as errors, prints the 69
axiom reports of `PublicVerification/Axioms.lean`, and checks them
(`scripts/check_public_axioms.py`). `lake build` alone builds the library. Further notes are in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

## Running the comparator

The comparator tools are pinned in
[`audit/comparator-tool-pins.json`](audit/comparator-tool-pins.json). On Linux, from a fresh
clone:

```bash
bash scripts/build_comparator_tools.sh <tools-dir>
COMPARATOR_TOOLS=<tools-dir> bash scripts/run_comparators.sh
```

The first command builds `leanprover/comparator`, `lean4export`, nanoda and landrun at the pinned
revisions; the second checks the pair and expects `Your solution is okay!`. The workflow
[`comparator.yml`](.github/workflows/comparator.yml) runs the same steps.

## Repository layout

```text
FiniteAvalanches/              the development: sandpiles and waves (Sandpile/), spanning trees
                               and Wilson's algorithm (Trees/, Wilson/), probability (Probability/,
                               MeasureTheory/), electrical networks and plane drawings
                               (Electrical/), the needle and revealed-roots estimates (Needle/,
                               RevealedRoots/), the paper's statements (Paper/, Statements/) and
                               the external results (External/)
FiniteAvalanchesCurrent/       the numbered statements of the paper, with Theorem 1.1 in
                               RegisteredPast/Main.lean
FiniteAvalanchesFrozen/, FiniteAvalanchesProofs/
                               Lemma 6.1 and its proof
CurrentSource/, CurrentRegisteredPast/, CurrentMain/, CurrentMean/, CurrentRootConsumers/,
Checks/ and the top-level modules
                               the electrical construction on the actual networks and the
                               assembly of Theorem 1.1
FiniteAvalanchesAudit/         the comparator challenge, solution and configuration
PublicVerification/Axioms.lean the axiom reports
audit/                         the registry of external inputs, the statement map, the source
                               inventory and the comparator tool pins
docs/                          verification.md and electrical-voltage.md
scripts/                       the build, axiom, input and comparator checks
.github/workflows/             build.yml and comparator.yml
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude), under the
direction of the author. The mathematics of the paper was developed with OpenAI models, as the
paper's statement on the use of artificial intelligence describes. Every proof is checked by the
Lean kernel. The models and tooling are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development and the paper are by **Ahmed Bou-Rabee**. To cite the formalization, use
[`CITATION.cff`](CITATION.cff); please also cite the paper.

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability); the comparator
audit uses [`leanprover/comparator`](https://github.com/leanprover/comparator). Third-party
notices are in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

## License

The Lean code is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper
source is not included in this repository.
