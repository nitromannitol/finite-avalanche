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

## Results from the literature

The registry [`audit/trusted-inputs.json`](audit/trusted-inputs.json) and the README list the 25
registered results from the literature. Theorem 1.1 assumes none of them: 22 are proved in Lean,
each with the statement text of the axiom it replaces, and the remaining three are axioms that
Theorem 1.1 does not use. Where the Lean proof of a registered result takes a different route from
the cited source, the route is recorded here.

- **The infinite-volume sandpile law** (`SandpileLimit.exists_infiniteVolumeLaw`; Athreya–Járai
  2004, Theorem 1 and Remark 1(iii), with the 2006 correction; Járai–Werning 2014, Theorem 3).
  Locality of the height events comes from the held burning of Lemma 2.1 and a factorization of
  the finite laws into inner and outer parts. The wired spanning trees converge along every
  exhaustion, by nested projection domination between boxes. Pasts are finite because the
  limiting tree has one end, and dual paths bound them uniformly. Translation invariance follows
  from the independence of the exhaustion
  ([`InfiniteVolumeLaw.lean`](FiniteAvalanches/Sandpile/Limit/InfiniteVolumeLaw.lean)).
- **One tree with one end** (`square_lattice_wired_ust_one_tree_one_end`; BLPS Theorem 12.4,
  Lyons–Peres Theorem 10.36). The primal and dual limits are trees. For a present edge, the dual
  tree path between the ends of its dual edge closes a dual trail; the sites whose rays cross the
  trail an odd number of times form a finite set that only this edge leaves. Hence every finite
  deletion leaves exactly one infinite component
  ([`WiredLimitOneEnd.lean`](FiniteAvalanches/Wilson/Lattice/WiredLimitOneEnd.lean)).
- **The tail of the path between adjacent sites**
  (`BarlowMasson2011.adjacent_ust_path_euclidean_tail`; Barlow–Masson 2011, Lemmas 2.4 and 2.6).
  The tree law is the limit of the laws of the wired boxes, and in each box Wilson's algorithm
  runs from roots on the exterior of the box. Lemma 2.4 follows the decomposition of Barlow and
  Masson by the prefix of the loop-erased path and the last visit. Its ratio bound uses a cone
  estimate from the exactly harmonic quadratic `Re z + Re z² / 2` and the maximum principle, explicit
  two-sided bounds on annuli from the potential kernel, and an inward Beurling estimate from the
  first-entrance decomposition and the symmetry of the Green function. The exponent `1/3`
  balances the reentry bound of Lemma 2.4 against the Beurling estimate
  ([`AdjacentPath.lean`](FiniteAvalanches/Walk/BarlowMasson/AdjacentPath.lean)).
- **The Beurling estimate** (`lawler_limic_beurling_srw_Z2`; Lawler–Limic 2004, Theorem 1, for the
  simple random walk) follows Sections 2 to 5 of Lawler and Limic. Lemma 2 uses that the walk
  exits the disk of radius `r` at distance less than `r + 1`. Lemma 3 (11) is the minimum
  principle with the potential kernel; Lemma 6 is proved for the segment `ℤ ∩ [-n, n)`. Lemma 10
  combines the product of Lemma 9, the exact strip value `1/(2n)` from gambler's ruin
  (Lawler–Limic 2010, 5.1.1) and a comparison of half-axes with factor 4. Lemma 11 (a) combines
  (8), Lemmas 3, 7 in `C_{4n}` and 8, and the Markov property at the exit of `C_n`; Lemma 11 (b) is
  proved for `|Im z| ≤ n` with the Green function of a half-plane and a renewal argument.
  Proposition 12 (a) reflects the walk after its last visit to the imaginary axis and swaps the
  coordinates; (b) uses reversal, 11 (a), 7 and 8; (22) uses the half-plane kernel; (c) bounds
  the first visit to the axis at `-k` by `O((n + k)^{-2})` and then applies (b); (d) is as
  printed; (e) is proved for `1 ≤ j ≤ n`, the range that Lemma 14 uses, through the first visit
  to `ℤ`. Lemma 13 and (29) compare affine functions of the potential kernel with the maximum
  principle, Lemma 14 solves `q ≤ K / log n + (1 - c) q`, and Section 5 gives the lower bound
  `c / log n` with inner radius `n` and distance in `[2n, 2n + 1)`
  ([`Estimate.lean`](FiniteAvalanches/Walk/Beurling/Estimate.lean),
  [`Position.lean`](FiniteAvalanches/Walk/Beurling/Position.lean)).
- **The faces of a two-pole plane network** (`finite_plane_two_pole_topology`; Mohar–Thomassen,
  pp. 87–91; Lyons–Peres, Proposition 9.4). The boundary telescoping is proved with the winding
  numbers of the fundamental cycles of a spanning tree: the winding number jumps across an edge by
  its signed passage at the edge chart, and the dual coboundaries are combinations of fundamental
  cycles. The orientation enters only through the oriented edge charts
  ([`FaceBoundaryLaw.lean`](FiniteAvalanches/Support/Plane/FaceBoundaryLaw.lean)).
- **The geometric dual** (`finite_plane_geometric_dual`; Mohar–Thomassen, Theorem 3.2.4 and
  Proposition 3.4.1). In each face, a simple arc through the starts of all crossing stubs is
  straightened and normalized to a square; the arms of the dual vertex are radial segments
  followed by the stubs after their last exit from the square. The construction uses neither
  2-connectivity nor facial walks
  ([`GeneralGeometricDual.lean`](FiniteAvalanches/Support/Plane/GeneralGeometricDual.lean)).
- **Extension and straightening of plane arcs** (`parametrized_plane_arc_straightening`;
  Mohar–Thomassen, Theorem 2.2.6). The image of a round disk is normalized to a round disk by
  splitting along a crosscut, applying the parametrized Jordan–Schönflies theorem to each part and
  gluing; the isotopy then comes from the local agreement at one point by conjugation with
  dilations ([`OrientedArcStraightening.lean`](FiniteAvalanches/Support/Plane/OrientedArcStraightening.lean)).
- **Redrawing a path of the outer face on a disk** (`outer_face_simple_path_disk_redrawing`). The
  path is straightened by the arc straightening above, and the drawing is built in a square normal
  form by induction on the number of edges; the Jordan curve theorem and the parametrized
  Jordan–Schönflies theorem give the one-side lemma and the base case
  ([`Assembly.lean`](FiniteAvalanches/Support/Plane/OuterRedrawing/Assembly.lean)).

- **Weak convergence of the wired spanning trees** (`square_lattice_wired_ust_weak_limit`) is
  derived from Wilson's algorithm on the wired boxes: explorations rooted at the origin and at the
  wired sink are coupled through cycle popping, and the probabilities of finite edge cylinders
  converge ([`FiniteUstWeakLimit.lean`](FiniteAvalanches/Wilson/Lattice/FiniteUstWeakLimit.lean)).
- **Planar duality of the spanning tree** (`square_lattice_ust_dual_law`) is proved in finite
  volume first: on each wired box, cut parity identifies the complements of spanning trees with
  spanning trees of the face graph, and the shifted face-tree laws converge to the wired law
  ([`WiredDualFaceCutParity.lean`](FiniteAvalanches/Wilson/Lattice/WiredDualFaceCutParity.lean)).
- **Wilson's algorithm with two root sets** (`wilson_two_color_law_existsUnique`) is proved by
  cycle popping on the finite networks, with the cylinder law constructed and shown unique on
  the recurrent lattice
  ([`WiredRootedSupport.lean`](FiniteAvalanches/Wilson/Lattice/WiredRootedSupport.lean)).
- **Pairing groves and response-matrix minors** (`kenyonWilson_pairingGroves_resistanceMinor`):
  Kenyon and Wilson derive the formula from their grove partition functions (Theorems 8.1 and
  B.3). The Lean proof instead uses the all-minors matrix-tree theorem and complementary minors of
  the grounded Green kernel
  ([`ResistanceComplement.lean`](FiniteAvalanches/Electrical/Trees/ResistanceComplement.lean),
  [`PairingRelabel.lean`](FiniteAvalanches/Electrical/Trees/PairingRelabel.lean)).
- **Plane topology.** The face star of a vertex, bonds as dual cycles, connectedness of the dual,
  complementary spanning trees and edge-chart incidence, and through them the four plane-graph
  results above, are proved from the Jordan–Schönflies theorem, in modules copied from Álvaro Begué's formalization
  ([`FiniteAvalanches/Support/Schoenflies/`](FiniteAvalanches/Support/Schoenflies/)). These proofs
  also use six planar-separation modules copied from Leonardo Bonanno's lean-formalizations at
  commit `31e7483`: the degree of a loop, Eilenberg's criterion, Janiszewski's theorem and the
  unbounded component ([`TopoDegree.lean`](FiniteAvalanches/Support/Plane/TopoDegree.lean),
  [`TopoEilenberg.lean`](FiniteAvalanches/Support/Plane/TopoEilenberg.lean),
  [`TopoJaniszewski.lean`](FiniteAvalanches/Support/Plane/TopoJaniszewski.lean),
  [`TopoSep.lean`](FiniteAvalanches/Support/Plane/TopoSep.lean),
  [`PlanarCore.lean`](FiniteAvalanches/Support/Plane/PlanarCore.lean) and
  [`Disconnect.lean`](FiniteAvalanches/Support/Plane/Disconnect.lean)). The two punctured-plane
  transport results are proved in this repository
  ([`PuncturedTransport.lean`](FiniteAvalanches/Support/Plane/PuncturedTransport.lean),
  [`ChartFaceTransport.lean`](FiniteAvalanches/Support/Plane/ChartFaceTransport.lean)); the chart-face
  transport uses the loop degree of `TopoDegree.lean`.
