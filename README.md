# Sandpile avalanches in two dimensions are finite

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*Sandpile avalanches in two dimensions are finite*](https://arxiv.org/abs/2610.13940),
> arXiv:2610.13940.

The formalized text is the arXiv v2 source (`main.tex`, SHA-256
`d2a875c154db9ff913ec6b25cf38e8da134ca977f6a24fd9c036cd8873b1082a`). All 17 numbered
statements of the paper are stated and proved in Lean, the main theorem among them. No result from
the literature is assumed by Theorem 1.1 or the other numbered statements: the 22 registered results
their proofs use are proved in Lean, as are two further registered results, and each of the 17
statements depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The
repository still declares one literature result as an axiom, the square tiling of Brooks, Smith,
Stone and Tutte, which none of the numbered statements uses (see
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

1. **Results from the literature.** No result from the literature is assumed by Theorem 1.1 or
   the other numbered statements. The results that their proofs cite are stated in [`FiniteAvalanches/External/`](FiniteAvalanches/External/) and
   proved there; the axiom report of Theorem 1.1 consists of `propext`, `Classical.choice` and
   `Quot.sound` only. The registry [`audit/trusted-inputs.json`](audit/trusted-inputs.json)
   records the exact Lean statement of each cited result, its hashes, its source references and
   the module that proves it. Each statement text is identical to that of the axiom it replaced.

   *Proved results from the literature (24).* Each depends only on `propext`,
   `Classical.choice` and `Quot.sound`. The first 22 are used by the proofs of the numbered
   statements; the last two are not.

   | Result | Lean theorem | Proof |
   | --- | --- | --- |
   | Existence of the infinite-volume sandpile law on `ℤ²` (Athreya–Járai 2004, with the 2006 correction; Járai–Werning 2014) | `SandpileLimit.exists_infiniteVolumeLaw` | held burning and one-ended spanning trees |
   | Weak convergence of the wired uniform spanning trees of the boxes (Pemantle; Häggström; BLPS; Lyons–Peres §10.1; Járai 2012) | `square_lattice_wired_ust_weak_limit` | Wilson's algorithm on the wired boxes |
   | The wired uniform spanning tree of `ℤ²` is one tree with one end (BLPS Theorem 12.4; Lyons–Peres Theorems 10.30, 10.36, 10.41) | `square_lattice_wired_ust_one_tree_one_end` | dual cycles and ray-crossing parity |
   | Planar duality of the uniform spanning tree (BLPS Theorem 12.2; Lyons–Peres §10.3) | `square_lattice_ust_dual_law` | finite tree complementation and weak limits |
   | Wilson's algorithm with two root sets (Lyons–Peres Theorem 4.1 and §4.2) | `wilson_two_color_law_existsUnique` | cycle popping |
   | The tail of the tree path between adjacent sites (Barlow–Masson 2011, Lemma 2.6) | `BarlowMasson2011.adjacent_ust_path_euclidean_tail` | Wilson's algorithm in wired boxes, reentry of loop-erased walk and the Beurling estimate |
   | The Beurling estimate for simple random walk on `ℤ²` (Lawler–Limic 2004, Theorem 1) | `lawler_limic_beurling_srw_Z2` | the argument of Lawler–Limic, Sections 2 to 5 |
   | Pairing groves and response-matrix minors (Kenyon–Wilson 2009, Theorems 8.1 and B.3) | `kenyonWilson_pairingGroves_resistanceMinor` | all-minors matrix-tree theorem |
   | The all-minors matrix-tree theorem (Chaiken 1982) | `allMinors_matrixTree` | Lattice-Probability |
   | Nested projection domination (Lyons 2003, Theorem 6.2) | `lyons_nestedProjectionDomination` | Lattice-Probability |
   | Disk alternation (Thomassen 1992, Lemmas 2.1 and 2.13) | `disk_alternation_impossible` | Lattice-Probability |
   | The faces of a two-pole plane network | `finite_plane_two_pole_topology` | winding numbers of fundamental cycles |
   | Extension and straightening of plane arcs | `parametrized_plane_arc_straightening` | Jordan–Schönflies theorem and a dilation isotopy |
   | Redrawing a path of the outer face on the boundary of a disk | `outer_face_simple_path_disk_redrawing` | a square normal form and induction on the edges |
   | The geometric dual | `finite_plane_geometric_dual` | arcs through the crossing sides of each face |
   | The face star of a vertex | `plane_vertex_face_star` | Jordan–Schönflies theorem |
   | Bonds as dual cycles | `finite_plane_dual_bond_cycle` | Jordan–Schönflies theorem |
   | Connectedness of the dual | `finite_plane_dual_connected` | Jordan–Schönflies theorem |
   | Complementary spanning trees | `finite_plane_tree_complement` | Jordan–Schönflies theorem |
   | The faces on both sides of an edge | `plane_edge_chart_incidence` | Jordan–Schönflies theorem |
   | Transport of faces under inversion of the punctured plane | `plane_punctured_face_transport`, `plane_punctured_chart_face_transport` | proved in this repository |
   | Wilson's algorithm on a finite network (Lyons–Peres Theorem 4.1) | `wilson_classical_tree_probability` | cycle popping, and the same law for stacks of copies and for a fresh row per walk |
   | Ray-seeded Wilson sampling on `ℤ²` (van Engelenburg–Hutchcroft 2023, Lemma 10) | `square_lattice_ray_seeded_wilson` | Wilson's algorithm rooted at a distant site, with the limit taken in the one-ended tree |

   Available references for the plane-graph results include Mohar–Thomassen, *Graphs on
   Surfaces*, Diestel, *Graph Theory*, and Hatcher, *Algebraic Topology*. The Jordan–Schönflies
   modules under `FiniteAvalanches/Support/Schoenflies/` are copied from Álvaro Begué's
   formalization. The plane-topology proofs, and the chart-face transport, also use six
   planar-separation modules (the degree of a loop, Eilenberg's criterion and Janiszewski's
   theorem) copied from Leonardo Bonanno's lean-formalizations; see [Copied code](#copied-code).
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md) records where a proof takes a different route from the
   cited source.

   The repository still declares one literature result as an axiom, registered in the same
   registry: the square tiling of Brooks, Smith, Stone and Tutte (`bsst_square_tiling`, in
   [`FiniteAvalanches/External/BSST.lean`](FiniteAvalanches/External/BSST.lean)). None of the 17
   numbered statements uses it. It is referenced by four auxiliary modules of
   `FiniteAvalanches/Electrical/Geometry/` outside the proof of every numbered statement:
   `SourceChartApplication`, `PhysicalTilingStream`, `PolarStream` and `PhysicalFaceStar`.
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
  checks each of them: Theorem 1.1 uses exactly the three standard axioms, the 24 proved results
  from the literature use only the standard axioms, and every other report lists only standard
  and registered axioms. The review-gated check requires a current source review.
- **Warning-free build.** The continuous-integration build compiles every module with warnings
  treated as errors.
- **Independent check of the statement.** The challenge in
  [`FiniteAvalanchesAudit/MainOrigin/`](FiniteAvalanchesAudit/MainOrigin/) imports mathlib alone
  and rebuilds Theorem 1.1 from recorded kernel data. The
  [leanprover/comparator](https://github.com/leanprover/comparator) check, with the Lean and
  nanoda kernels, passed in continuous integration for the earlier sources with 19 and with 8
  literature inputs and for the previous source without literature inputs, whose pair permits
  exactly the three standard axioms. The current source leaves this pair unchanged: a fresh
  capture of Theorem 1.1 reproduces it exactly. The pair has been independently reviewed for the
  current source; its comparator check runs in continuous integration.
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability
  `68722ce2d464119e90b373829d2761624b1f6a75`, recorded in [`lake-manifest.json`](lake-manifest.json).
- **Pinned statements and inputs.** [`audit/current-statements.json`](audit/current-statements.json)
  records, for each numbered statement, the line range and SHA-256 of its source in the paper and
  the hash of its Lean declaration; [`audit/source-inventory.json`](audit/source-inventory.json)
  records the hash of every production file.

[`docs/verification.md`](docs/verification.md) describes the checks in more detail.

## Size

About 254,300 lines of Lean in 1,553 files, of which about 200,700 lines are code once comments
and blank lines are removed, on top of mathlib and Lattice-Probability. The comparator surface under
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

The comparator run requires a current review of the source inventory. The first command builds
`leanprover/comparator`, `lean4export`, nanoda and landrun at the pinned
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

## Copied code

Some modules are copied from other repositories, with attribution and never through a Lake
dependency. Each copied file starts with a header naming its source repository, module path and
commit and the changes made; [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) lists them.

| Source | Commit | Files in this repository |
| --- | --- | --- |
| Álvaro Begué, [schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean) (Apache License 2.0, text in [`FiniteAvalanches/Support/Schoenflies/LICENSE`](FiniteAvalanches/Support/Schoenflies/LICENSE)) | `05a43d29cde026618777db3d4e4316204ccca237` | the 128 modules under `FiniteAvalanches/Support/Schoenflies/` |
| Leonardo Bonanno, [lean-formalizations](https://github.com/leobon12/lean-formalizations) (no licence stated upstream) | `31e748330ee154d5f41537c4b01f71b8a5510c2d` | `FiniteAvalanches/Support/Plane/`: `Disconnect`, `PlanarCore`, `TopoDegree`, `TopoEilenberg`, `TopoJaniszewski`, `TopoSep` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (Apache License 2.0) | `0b6994229ccf31047ae7b654ecbec59496594700` | `FiniteAvalanches/Support/Plane/`: `FinitePointComplement`, `LocalFaceIncidence`; `FiniteAvalanches/Wilson/`: `LoopErasureComposition`, `CyclePopping/Basic`, `CyclePopping/Erasure`, `CyclePopping/Trace` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (Apache License 2.0) | `99cfc20cb60d38c947523641e991a84350e77309` | `FiniteAvalanches/Walk/`: `SiteTranslation`, `IidBlocks`, `EuclidNormCoord` (one lemma) |

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
