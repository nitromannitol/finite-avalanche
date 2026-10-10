# Paper–Lean correspondence

All 16 numbered statements in manuscript revision `d2fc033` have proved declarations relative to 26 external inputs. The two local/revealed-root statements share one declaration and one constant.

| Paper statement | Lean declaration | Status |
| --- | --- | --- |
| `th:main` | [`FiniteAvalanchesFrozen.Main.finite_avalanches_origin_v3`](FiniteAvalanchesFrozen/MainOriginV3.lean) | Proved |
| `fv:held-burning` | [`FiniteAvalanches.Paper.SectionThree.held_burning`](FiniteAvalanches/Paper/SectionThree/HeldBurning.lean) | Proved |
| `fo:lattice-monotonicity` | [`FiniteAvalanches.Paper.Revision480.ActualSource.source_four_sets_global_mono`](FiniteAvalanches/Paper/Revision480/LatticeColorMonotonicity.lean) | Proved |
| `sp:reciprocal-reduction` | [`FiniteAvalanches.Paper.RevisionB972.reciprocal_reduction_limsup_v2`](FiniteAvalanches/Paper/RevisionB972/FiniteLimsupStatement.lean) | Proved |
| `rd:conditional-law` | [`FiniteAvalanches.Paper.Revision0F522C0.finite_conditional_contact_count_law`](FiniteAvalanches/Paper/Revision0F522C0/FiniteConditionalStatement.lean) | Proved |
| `ct:reciprocal` | [`FiniteAvalanches.Wilson.Lattice.SourceTargets.forest_reciprocal_cofinite_v4`](FiniteAvalanchesFrozen/ForestReciprocalCofiniteV4.lean) | Proved |
| `fv:inverse-waves` | [`FiniteAvalanches.Paper.Revision4498.wave_counts_eq_core_forward`](FiniteAvalanches/Paper/Revision4498/InverseWaves.lean) | Proved |
| `fv:outflow` | [`FiniteAvalanches.Paper.Revision4498.outflow_card_le_treeCount_mul_reciprocal`](FiniteAvalanches/Paper/Revision4498/Outflow.lean) | Proved |
| `rd:past-tail` | [`FiniteAvalanches.Paper.Revision4498.past_outside_origin_box_bound`](FiniteAvalanches/Paper/Revision4498/PastTail.lean) | Proved |
| `fo:local-comparison` | [`FiniteAvalanches.Wilson.Lattice.SourceTargets.local_comparison_and_revealed_roots_v4`](FiniteAvalanchesFrozen/JointCofiniteV4.lean) | Proved |
| `el:reference-moment` | [`FiniteAvalanches.Electrical.Source.Reference.reference_moment_v4`](FiniteAvalanchesFrozen/ElectricalReferenceMomentV4.lean) | Proved |
| `ct:needle` | [`FiniteAvalanchesFrozen.Needle107V4.connected_set_conductance_107`](FiniteAvalanchesFrozen/Needle107V4.lean) | Proved |
| `ct:revealed-roots` | [`FiniteAvalanches.Wilson.Lattice.SourceTargets.local_comparison_and_revealed_roots_v4`](FiniteAvalanchesFrozen/JointCofiniteV4.lean) | Proved |
| `el:pair-contact` | [`FiniteAvalanches.Electrical.Source.pair_contact_v2`](FiniteAvalanchesFrozen/ElectricalPairContactV2.lean) | Proved |
| `el:arc-moment` | [`FiniteAvalanches.Electrical.Source.arc_moment_v6`](FiniteAvalanchesFrozen/ElectricalArcMomentV6.lean) | Proved |
| `el:split-estimate` | [`FiniteAvalanches.Electrical.Source.split_estimate_v2`](FiniteAvalanchesFrozen/ElectricalSplitEstimateV2.lean) | Proved |

The exact source-facing declarations are linked above. Routine formal details are factored into supporting lemmas. The 26 standard inputs remain explicitly disclosed assumptions.
