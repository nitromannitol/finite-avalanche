# Manuscript correspondence

This map proposes exact Lean exports for the final round61 manuscript's 17 numbered statements. Source statement and proof hashes are extracted from the exact manuscript without notation normalization. Final type, definition, characterization, proof-route, consumption and axiom review is **PENDING**. File identity or compilation alone does not establish source correspondence.

| Source label | Lean export | Source |
| --- | --- | --- |
| `th:main` | `FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin` | [declaration](FiniteAvalanchesCurrent/RegisteredPast/Main.lean) |
| `fv:held-burning` | `FiniteAvalanchesCurrent.HeldBurning.held_burning` | [declaration](FiniteAvalanchesCurrent/HeldBurningV1.lean) |
| `fo:lattice-monotonicity` | `FiniteAvalanches.Paper.CurrentSource.global_monotonicity` | [declaration](FiniteAvalanchesCurrent/GlobalMonotonicity.lean) |
| `sp:reciprocal-reduction` | `FiniteAvalanches.Paper.RegisteredPast.FullInteger.reciprocal_reduction_limsup` | [declaration](FiniteAvalanchesCurrent/RegisteredPast/Reduction.lean) |
| `ct:reciprocal` | `FiniteAvalanches.Paper.CurrentSource.forest_reciprocal_cofinite` | [declaration](FiniteAvalanchesCurrent/ForestReciprocalV5.lean) |
| `rd:conditional-law` | `FiniteAvalanches.Paper.Current.finite_conditional_extended_contact_law` | [declaration](FiniteAvalanches/Paper/Current/ConditionalExtendedContacts.lean) |
| `fv:inverse-waves` | `FiniteAvalanchesCurrent.Punctured.inverse_waves` | [declaration](FiniteAvalanchesCurrent/InverseWavesV1.lean) |
| `fv:outflow` | `FiniteAvalanchesCurrent.Punctured.outflow` | [declaration](FiniteAvalanchesCurrent/OutflowV1.lean) |
| `rd:past-tail` | `FiniteAvalanches.Paper.Revision4498.past_outside_origin_box_bound` | [declaration](FiniteAvalanches/Paper/Revision4498/PastTail.lean) |
| `fo:local-comparison` | `FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed` | [declaration](FiniteAvalanches/Wilson/Lattice/CurrentForestJoint.lean) |
| `el:reference-moment` | `FiniteAvalanches.Electrical.Source.Reference.reference_moment_current` | [declaration](CurrentSource/ReferenceMomentCurrent.lean) |
| `ct:needle` | `FiniteAvalanchesFrozen.NeedlePathV5.needle_path` | [declaration](FiniteAvalanchesFrozen/NeedlePathV5.lean) |
| `ct:revealed-roots` | `FiniteAvalanches.Wilson.Lattice.CurrentForestJoint.local_and_revealed` | [declaration](FiniteAvalanches/Wilson/Lattice/CurrentForestJoint.lean) |
| `el:means` | `FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment.boundary_means` | [declaration](FiniteAvalanches/Electrical/Reference/BoundaryMeans.lean) |
| `el:pair-contact` | `FiniteAvalanches.Electrical.Source.pair_contact_current` | [declaration](FiniteAvalanches/Electrical/PairContact/Current.lean) |
| `el:arc-moment` | `FiniteAvalanches.Electrical.CurrentSourceRoots.arc_variance_expectations` | [declaration](FiniteAvalanchesCurrent/ArcMomentExpectations.lean) |
| `el:split-estimate` | `FiniteAvalanches.Electrical.CurrentSourceRoots.split_estimate_expectations` | [declaration](FiniteAvalanchesCurrent/SplitEstimateExpectations.lean) |

The means lemma is one semantic unit with its [source-drawing theorem](FiniteAvalanches/Electrical/Reference/ConjugateMeans.lean): all original edge copies, signed boundary means, and total mean equal to the grounded Green diagonal and original energy. The literal-expectation arc and split successors consume the [boundary expectation theorem](FiniteAvalanches/Electrical/Source/BoundaryExpectation.lean); a [normalization consumer](FiniteAvalanchesCurrent/BoundaryMeanApplication.lean) exercises its actual positive mean and nonzero tree cardinality.

Main and reduction use all signed integer fields. Main preserves one exponent and constant before all real thresholds. Local comparison and revealed roots share one declaration and epsilon. Global monotonicity uses A ⊆ A′ and Γ′ ⊆ Γ. The electrical construction adapts Lovász, *Graphs and Geometry*, §6.1/Theorem 6.1; the BSST assumption remains registered and unused by Main.
