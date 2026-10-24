# Paper ↔ Lean correspondence

The Lean statements follow the arXiv v2 source of the paper (`main.tex`, SHA-256
`d2a875c154db9ff913ec6b25cf38e8da134ca977f6a24fd9c036cd8873b1082a`). The line numbers below refer
to that file. [`audit/current-statements.json`](audit/current-statements.json) records, for each
statement, the SHA-256 of its source lines and of its proof in the paper and the hash of its Lean
declaration.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 (`th:main`, lines 51–56) | [`FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin`](FiniteAvalanchesCurrent/RegisteredPast/Main.lean) |
| Lemma 2.1 (`fv:held-burning`, lines 205–207) | [`FiniteAvalanchesCurrent.HeldBurning.held_burning`](FiniteAvalanchesCurrent/HeldBurningV1.lean) |
| Lemma 2.2 (`fo:lattice-monotonicity`, lines 227–229) | [`FiniteAvalanches.Paper.CurrentSource.global_monotonicity`](FiniteAvalanchesCurrent/GlobalMonotonicity.lean) |
| Proposition 3.1 (`sp:reciprocal-reduction`, lines 253–258) | [`FiniteAvalanches.Paper.RegisteredPast.FullInteger.reciprocal_reduction_limsup`](FiniteAvalanchesCurrent/RegisteredPast/Reduction.lean) |
| Proposition 3.2 (`ct:reciprocal`, lines 262–267) | [`FiniteAvalanches.Paper.CurrentSource.forest_reciprocal_cofinite`](FiniteAvalanchesCurrent/ForestReciprocalV5.lean) |
| Lemma 3.3 (`rd:conditional-law`, lines 271–273) | [`FiniteAvalanches.Paper.Current.finite_conditional_extended_contact_law`](FiniteAvalanches/Paper/Current/ConditionalExtendedContacts.lean) |
| Lemma 4.1 (`fv:inverse-waves`, lines 300–302) | [`FiniteAvalanchesCurrent.Punctured.inverse_waves`](FiniteAvalanchesCurrent/InverseWavesV1.lean) |
| Lemma 4.2 (`fv:outflow`, lines 343–348) | [`FiniteAvalanchesCurrent.Punctured.outflow`](FiniteAvalanchesCurrent/OutflowV1.lean) |
| Lemma 4.3 (`rd:past-tail`, lines 372–374) | [`FiniteAvalanches.Paper.Revision4498.past_outside_origin_box_bound`](FiniteAvalanches/Paper/Revision4498/PastTail.lean) |
| Proposition 5.1 (`fo:local-comparison`, lines 398–403) | [`FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed`](FiniteAvalanches/Wilson/Lattice/CurrentForestJoint.lean) |
| Proposition 5.2 (`el:reference-moment`, lines 414–419) | [`FiniteAvalanches.Electrical.Source.Reference.reference_moment_current`](CurrentSource/ReferenceMomentCurrent.lean) |
| Lemma 6.1 (`ct:needle`, lines 457–459) | [`FiniteAvalanchesFrozen.NeedlePathV5.needle_path`](FiniteAvalanchesFrozen/NeedlePathV5.lean) |
| Lemma 6.2 (`ct:revealed-roots`, lines 471–473) | [`FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed`](FiniteAvalanches/Wilson/Lattice/CurrentForestJoint.lean) |
| Lemma 7.1 (`el:means`, lines 557–571) | [`FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means`](FiniteAvalanches/Electrical/Reference/BoundaryMeans.lean) |
| Lemma 7.2 (`el:pair-contact`, lines 583–592) | [`FiniteAvalanches.Electrical.Source.pair_contact_current`](FiniteAvalanches/Electrical/PairContact/Current.lean) |
| Lemma 7.3 (`el:arc-moment`, lines 633–638) | [`FiniteAvalanches.Electrical.CurrentSourceRoots.arc_variance_expectations`](FiniteAvalanchesCurrent/ArcMomentExpectations.lean) |
| Lemma 7.4 (`el:split-estimate`, lines 683–688) | [`FiniteAvalanches.Electrical.CurrentSourceRoots.split_estimate_expectations`](FiniteAvalanchesCurrent/SplitEstimateExpectations.lean) |

## Readings

- **Theorem 1.1 and Proposition 3.1** are stated for the stationary law on all integer fields
  `ℤ² → ℤ`. Theorem 1.1 chooses its exponent `a` and constant `C` once, before every real
  threshold `M ≥ 0`.
- **Lemma 2.2** is stated for sets `A ⊆ A′` and `Γ′ ⊆ Γ`, as printed, and concludes stochastic
  domination of the forest laws and of the law of `𝓛(V)` for every `V`.
- **Proposition 5.1 and Lemma 6.2** are proved as one declaration, `local_and_revealed`, so that
  they share the constant `ε`, as in the paper.
- **Lemma 7.1** is proved with its companion
  [`ConjugateMeans.lean`](FiniteAvalanches/Electrical/Reference/ConjugateMeans.lean): the
  conjugacy identity holds for every copy of an original edge, and the total mean equals the
  grounded Green diagonal and the energy of the voltage. Lemmas 7.3 and 7.4 use the expectations
  of the boundary indicators as printed, through
  [`BoundaryExpectation.lean`](FiniteAvalanches/Electrical/Source/BoundaryExpectation.lean).
- **Electrical networks** keep every copy of a parallel edge; the voltage is defined for distinct
  terminals ([`docs/electrical-voltage.md`](docs/electrical-voltage.md)). The construction of the
  square tiling follows Lovász, *Graphs and Geometry*, §6.1 and Theorem 6.1.

The 22 standard results that the proofs use are listed in the README and in
[`audit/trusted-inputs.json`](audit/trusted-inputs.json).
